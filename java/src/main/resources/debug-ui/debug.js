/**
 * Petri Net Debugger - WebSocket Client
 *
 * Handles WebSocket communication, diagram rendering, and UI state management.
 */

// ======================== Configuration ========================

const CONFIG = {
    wsReconnectDelay: 2000,
    maxEventLogSize: 500,
    maxPlaybackDelay: 2000,
    minPlaybackDelay: 10,
    sliderResolution: 10000
};

// ======================== State ========================

const state = {
    ws: null,
    connected: false,
    currentSessionId: null,
    paused: false,
    speed: 1.0,
    eventIndex: 0,
    totalEvents: 0,
    marking: {},
    enabledTransitions: [],
    inFlightTransitions: [],
    mermaidDiagram: null,
    events: [],
    panzoomInstance: null,
    // Replay mode state
    playbackTimer: null,
    playbackAnimationFrame: null,  // rAF handle for smooth slider animation
    playbackStartTime: 0,         // timestamp when current delay started
    playbackDelay: 0,             // duration of current delay (ms)
    playbackFromIndex: 0,         // event index at start of current delay
    allReplayEvents: [],
    isReplayMode: false,
    // Filter state
    filter: {
        eventTypes: [],
        transitionNames: [],
        placeNames: []
    },
    // Search state
    searchTerm: '',
    searchMatches: [],       // indices of matching events in DOM
    currentMatchIndex: -1,
    // Breakpoint state
    breakpoints: [],
    // Net structure - authoritative mapping from names to Mermaid IDs
    netStructure: {
        places: [],      // [{name, mermaidId, tokenType, isStart, isEnd}]
        transitions: [], // [{name, mermaidId}]
        byMermaidId: {}  // Lookup: mermaidId → {name, isTransition, ...}
    },
    // SVG node cache - built once after renderMermaidDiagram(), eliminates DOM queries per event
    /** @type {null | {nodesByName: Map<string, Element>, nodesByMermaidId: Map<string, Element>, edgesByMermaidId: Map<string, Element[]>, allNodeShapes: Element[], allEdgePaths: Element[]}} */
    svgNodeCache: null,
    // Dirty flag for diagram highlighting - avoids redundant updateDiagramHighlighting() calls
    highlightDirty: false,
    // Checkpoint state for efficient seeking
    checkpoints: [],
    checkpointInterval: 50
};

// ======================== Playback Control (Frontend-Driven) ========================

function startPlayback() {
    if (state.playbackTimer || !state.isReplayMode) return;
    scheduleNextEvent();
}

function scheduleNextEvent() {
    if (state.eventIndex >= state.allReplayEvents.length) {
        stopPlayback();
        state.paused = true;
        updatePlaybackControls();
        return;
    }

    const event = state.allReplayEvents[state.eventIndex];

    // Apply event and advance index BEFORE checking breakpoints (apply-then-pause)
    applyEventToState(event);
    if (matchesClientFilter(event)) {
        addEventToLog(event, state.eventIndex);
    }
    state.eventIndex++;
    updateMarkingInspector();
    updateTimelinePosition();

    // Check breakpoints AFTER applying - pause on the event that triggered the breakpoint
    const hitBp = checkClientBreakpoints(event);
    if (hitBp) {
        stopPlayback();
        state.paused = true;
        updatePlaybackControls();
        highlightBreakpointInList(hitBp.id);
        showBreakpointNotification(hitBp.id, event);
        return;
    }

    // End of events check after advancing
    if (state.eventIndex >= state.allReplayEvents.length) {
        stopPlayback();
        state.paused = true;
        updatePlaybackControls();
        return;
    }

    // Compute delay based on real timestamps to next event
    const nextEvent = state.allReplayEvents[state.eventIndex];
    const delay = computePlaybackDelay(event, nextEvent);

    startSliderAnimation(state.eventIndex, delay);
    state.playbackTimer = setTimeout(() => {
        state.playbackTimer = null;
        scheduleNextEvent();
    }, delay);
}

function computePlaybackDelay(currentEvent, nextEvent) {
    const currentTs = currentEvent.timestamp ? new Date(currentEvent.timestamp).getTime() : 0;
    const nextTs = nextEvent.timestamp ? new Date(nextEvent.timestamp).getTime() : 0;
    const realDelta = nextTs - currentTs;

    // Clamp to [0, maxPlaybackDelay], scale by speed, floor at minPlaybackDelay
    const clamped = Math.max(0, Math.min(realDelta, CONFIG.maxPlaybackDelay));
    const scaled = clamped / state.speed;
    return Math.max(scaled, CONFIG.minPlaybackDelay);
}

function stopPlayback() {
    if (state.playbackTimer) {
        clearTimeout(state.playbackTimer);
        state.playbackTimer = null;
    }
    stopSliderAnimation();
}

function startSliderAnimation(fromIndex, delay) {
    stopSliderAnimation();
    state.playbackStartTime = performance.now();
    state.playbackDelay = delay;
    state.playbackFromIndex = fromIndex;

    function animate() {
        const elapsed = performance.now() - state.playbackStartTime;
        const progress = Math.min(elapsed / state.playbackDelay, 1);
        const interpolated = state.playbackFromIndex + progress;

        const slider = document.getElementById('timeline-slider');
        slider.value = state.totalEvents > 0
            ? (interpolated / state.totalEvents) * CONFIG.sliderResolution
            : 0;

        if (progress < 1) {
            state.playbackAnimationFrame = requestAnimationFrame(animate);
        }
    }
    state.playbackAnimationFrame = requestAnimationFrame(animate);
}

function stopSliderAnimation() {
    if (state.playbackAnimationFrame) {
        cancelAnimationFrame(state.playbackAnimationFrame);
        state.playbackAnimationFrame = null;
    }
}

/**
 * Builds periodic checkpoints of the net state for efficient seeking.
 * Called when replay events arrive. Every `checkpointInterval` events,
 * snapshots the marking, enabled transitions, and in-flight transitions.
 *
 * @param {number} [fromIndex=0] - Start processing from this event index.
 *   When called incrementally, pass the previous allReplayEvents length
 *   to avoid reprocessing all events from scratch.
 */
function buildCheckpoints(fromIndex = 0) {
    // Restore temp state from last checkpoint, or start fresh
    const tempMarking = {};
    const tempEnabled = [];
    const tempInFlight = [];
    let startIndex = 0;

    if (fromIndex > 0 && state.checkpoints.length > 0) {
        const lastCp = state.checkpoints[state.checkpoints.length - 1];
        Object.assign(tempMarking, structuredClone(lastCp.marking));
        tempEnabled.push(...lastCp.enabledTransitions);
        tempInFlight.push(...lastCp.inFlightTransitions);
        startIndex = lastCp.index;
    } else {
        // Full rebuild
        state.checkpoints = [];
    }

    // Process events from startIndex (or 0 on full rebuild)
    for (let i = startIndex; i < state.allReplayEvents.length; i++) {
        const event = state.allReplayEvents[i];
        // Inline state application on temp state
        switch (event.type) {
            case 'TokenAdded':
                if (!tempMarking[event.placeName]) tempMarking[event.placeName] = [];
                tempMarking[event.placeName].push(event.details.token);
                break;
            case 'TokenRemoved':
                if (tempMarking[event.placeName]?.length > 0) tempMarking[event.placeName].shift();
                break;
            case 'TransitionEnabled':
                if (!tempEnabled.includes(event.transitionName)) tempEnabled.push(event.transitionName);
                break;
            case 'TransitionStarted': {
                const idx = tempEnabled.indexOf(event.transitionName);
                if (idx >= 0) tempEnabled.splice(idx, 1);
                if (!tempInFlight.includes(event.transitionName)) tempInFlight.push(event.transitionName);
                break;
            }
            case 'TransitionCompleted':
            case 'TransitionFailed':
            case 'TransitionTimedOut':
            case 'ActionTimedOut': {
                const idx2 = tempInFlight.indexOf(event.transitionName);
                if (idx2 >= 0) tempInFlight.splice(idx2, 1);
                break;
            }
            case 'MarkingSnapshot':
                // Replace marking entirely
                Object.keys(tempMarking).forEach(k => delete tempMarking[k]);
                Object.assign(tempMarking, event.details.marking || {});
                break;
        }

        // Snapshot every checkpointInterval events (at end of event i, representing state after i+1 events applied)
        if ((i + 1) % state.checkpointInterval === 0) {
            state.checkpoints.push({
                index: i + 1,
                marking: structuredClone(tempMarking),
                enabledTransitions: [...tempEnabled],
                inFlightTransitions: [...tempInFlight]
            });
        }
    }
}

function seekToIndex(targetIndex) {
    stopPlayback();

    // Find nearest checkpoint ≤ targetIndex
    let startIndex = 0;
    state.marking = {};
    state.enabledTransitions = [];
    state.inFlightTransitions = [];

    for (let i = state.checkpoints.length - 1; i >= 0; i--) {
        if (state.checkpoints[i].index <= targetIndex) {
            const cp = state.checkpoints[i];
            startIndex = cp.index;
            state.marking = structuredClone(cp.marking);
            state.enabledTransitions = [...cp.enabledTransitions];
            state.inFlightTransitions = [...cp.inFlightTransitions];
            break;
        }
    }

    // Replay only the remaining events from checkpoint to target
    for (let i = startIndex; i < targetIndex && i < state.allReplayEvents.length; i++) {
        applyEventToState(state.allReplayEvents[i]);
    }

    state.eventIndex = targetIndex;

    // Re-render event log
    reRenderEventLog();

    state.highlightDirty = true;
    updateMarkingInspector();
    updateTimelinePosition();
}

// ======================== WebSocket Management ========================

function connect() {
    const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
    const wsUrl = `${protocol}//${window.location.host}/debug/petri`;

    console.log('Connecting to WebSocket:', wsUrl);
    state.ws = new WebSocket(wsUrl);

    state.ws.onopen = () => {
        console.log('WebSocket connected');
        state.connected = true;
        updateConnectionStatus(true);
        refreshSessions();
    };

    state.ws.onclose = (event) => {
        console.log('WebSocket closed:', event.code, event.reason);
        state.connected = false;
        updateConnectionStatus(false);
        setTimeout(connect, CONFIG.wsReconnectDelay);
    };

    state.ws.onerror = (error) => {
        console.error('WebSocket error:', error);
    };

    state.ws.onmessage = (event) => {
        try {
            const response = JSON.parse(event.data);
            handleResponse(response);
        } catch (e) {
            console.error('Failed to parse WebSocket message:', e);
        }
    };
}

function send(command) {
    if (state.ws && state.ws.readyState === WebSocket.OPEN) {
        state.ws.send(JSON.stringify(command));
    } else {
        console.warn('WebSocket not connected');
    }
}

// ======================== Response Handlers ========================

function handleResponse(response) {
    console.debug('Received response:', response.type, response);

    switch (response.type) {
        case 'sessionList':
            handleSessionList(response);
            break;
        case 'subscribed':
            handleSubscribed(response);
            break;
        case 'unsubscribed':
            handleUnsubscribed(response);
            break;
        case 'event':
            handleEvent(response);
            break;
        case 'eventBatch':
            handleEventBatch(response);
            break;
        case 'markingSnapshot':
            handleMarkingSnapshot(response);
            break;
        case 'playbackStateChanged':
            handlePlaybackStateChanged(response);
            break;
        case 'filterApplied':
            handleFilterApplied(response);
            break;
        case 'breakpointHit':
            handleBreakpointHit(response);
            break;
        case 'breakpointList':
            handleBreakpointList(response);
            break;
        case 'breakpointSet':
            handleBreakpointSet(response);
            break;
        case 'breakpointCleared':
            handleBreakpointCleared(response);
            break;
        case 'error':
            handleError(response);
            break;
        default:
            console.warn('Unknown response type:', response.type);
    }
}

function handleSessionList(response) {
    const select = document.getElementById('session-select');
    const currentValue = select.value;

    // Clear existing options except placeholder
    select.innerHTML = '<option value="">Select a session...</option>';

    // Add sessions
    response.sessions.forEach(session => {
        const option = document.createElement('option');
        option.value = session.sessionId;
        const status = session.active ? '(live)' : '(ended)';
        const time = new Date(session.startTime).toLocaleTimeString();
        option.textContent = `${session.netName} ${status} - ${time} (${session.eventCount} events)`;
        select.appendChild(option);
    });

    // Restore selection if still valid
    if (currentValue && select.querySelector(`option[value="${currentValue}"]`)) {
        select.value = currentValue;
    }
}

function handleSubscribed(response) {
    console.log('Subscribed to session:', response.sessionId);

    state.currentSessionId = response.sessionId;
    state.mermaidDiagram = response.mermaidDiagram;
    state.marking = response.currentMarking || {};
    state.enabledTransitions = response.enabledTransitions || [];
    state.inFlightTransitions = response.inFlightTransitions || [];
    state.totalEvents = response.eventCount;
    state.events = [];
    state.eventIndex = 0;
    state.breakpoints = []; // Reset breakpoints for new session

    // Build mermaidId → structure lookup from server-provided structure
    if (response.structure) {
        state.netStructure = {
            places: response.structure.places || [],
            transitions: response.structure.transitions || [],
            byMermaidId: {}
        };

        // Index places by mermaidId
        state.netStructure.places.forEach(p => {
            state.netStructure.byMermaidId[p.mermaidId] = {
                name: p.name,
                isTransition: false,
                tokenType: p.tokenType,
                isStart: p.isStart,
                isEnd: p.isEnd
            };
        });

        // Index transitions by mermaidId
        state.netStructure.transitions.forEach(t => {
            state.netStructure.byMermaidId[t.mermaidId] = {
                name: t.name,
                isTransition: true
            };
        });

        console.log('Net structure loaded:', state.netStructure.places.length, 'places,',
            state.netStructure.transitions.length, 'transitions');
    } else {
        // Reset structure if not provided
        state.netStructure = { places: [], transitions: [], byMermaidId: {} };
    }

    // Initialize replay mode state
    state.isReplayMode = document.getElementById('mode-select').value === 'replay';
    if (state.isReplayMode) {
        state.allReplayEvents = [];
        state.paused = true; // Start paused in replay mode
        state.marking = {}; // Reset marking for replay - will be rebuilt as events play
        state.enabledTransitions = []; // Reset enabled transitions for replay
        state.inFlightTransitions = []; // Reset in-flight transitions for replay
        stopPlayback(); // Ensure no timer is running
    }

    // Render diagram
    renderMermaidDiagram(response.mermaidDiagram);

    // Update UI
    updateMarkingInspector();
    updateTimelinePosition();
    updatePlaybackControls();
    enableControls(true);
    renderBreakpointList();
    updateAutocompleteOptions();

    document.getElementById('no-session').classList.add('hidden');
}

function handleUnsubscribed(response) {
    console.log('Unsubscribed from session:', response.sessionId);

    if (state.currentSessionId === response.sessionId) {
        state.currentSessionId = null;
        state.mermaidDiagram = null;
        state.marking = {};
        state.events = [];
        state.svgNodeCache = null;
        state.checkpoints = [];
        enableControls(false);
        document.getElementById('no-session').classList.remove('hidden');
        document.getElementById('mermaid-diagram').innerHTML = '';
    }
}

function handleEvent(response) {
    if (response.sessionId !== state.currentSessionId) return;

    state.events.push(response.event);
    state.eventIndex = response.index + 1;

    // Update state based on event
    applyEventToState(response.event);

    // Update UI
    addEventToLog(response.event, response.index);
    updateMarkingInspector();
    updateTimelinePosition();

    // Trim event log if too large
    if (state.events.length > CONFIG.maxEventLogSize) {
        state.events.shift();
        const eventLog = document.getElementById('event-log');
        if (eventLog.firstChild) {
            eventLog.removeChild(eventLog.firstChild);
        }
    }
}

function handleEventBatch(response) {
    if (response.sessionId !== state.currentSessionId) return;

    if (state.isReplayMode) {
        // Store all events for replay - don't immediately display
        const prevLength = state.allReplayEvents.length;
        state.allReplayEvents.push(...response.events);
        state.totalEvents = state.allReplayEvents.length;
        buildCheckpoints(prevLength);
        updateTimelinePosition();
    } else {
        // Live mode - display events immediately
        response.events.forEach((event, i) => {
            state.events.push(event);
            applyEventToState(event);
            addEventToLog(event, response.startIndex + i);
        });

        state.eventIndex = response.startIndex + response.events.length;
        updateMarkingInspector();
        updateTimelinePosition();
    }

    // Update autocomplete with new transition/place names from events
    updateAutocompleteOptions();
}

function handleMarkingSnapshot(response) {
    if (response.sessionId !== state.currentSessionId) return;

    state.marking = response.marking || {};
    state.enabledTransitions = response.enabledTransitions || [];
    state.inFlightTransitions = response.inFlightTransitions || [];
    updateMarkingInspector();
}

function handlePlaybackStateChanged(response) {
    if (response.sessionId !== state.currentSessionId) return;

    state.paused = response.paused;
    state.speed = response.speed;
    state.eventIndex = response.currentIndex;

    updatePlaybackControls();
    updateSpeedButtons();
    updateTimelinePosition();
}

function handleFilterApplied(response) {
    if (response.sessionId !== state.currentSessionId) return;

    console.log('Filter applied:', response.filter);
    // Update local filter state to match server
    if (response.filter) {
        state.filter = {
            eventTypes: response.filter.eventTypes || [],
            transitionNames: response.filter.transitionNames || [],
            placeNames: response.filter.placeNames || []
        };
    } else {
        state.filter = { eventTypes: [], transitionNames: [], placeNames: [] };
    }
    updateFilterUI();
}

function handleBreakpointHit(response) {
    if (response.sessionId !== state.currentSessionId) return;

    console.log('Breakpoint hit:', response.breakpointId, response.event);
    state.paused = true;
    updatePlaybackControls();

    // Highlight the breakpoint in the list
    highlightBreakpointInList(response.breakpointId);

    // Flash the event in the log
    showBreakpointNotification(response.breakpointId, response.event);
}

function handleBreakpointList(response) {
    if (response.sessionId !== state.currentSessionId) return;

    state.breakpoints = response.breakpoints || [];
    renderBreakpointList();
}

function handleBreakpointSet(response) {
    if (response.sessionId !== state.currentSessionId) return;

    // Add to local state if not already present
    const exists = state.breakpoints.find(bp => bp.id === response.breakpoint.id);
    if (!exists) {
        state.breakpoints.push(response.breakpoint);
    }
    renderBreakpointList();
}

function handleBreakpointCleared(response) {
    if (response.sessionId !== state.currentSessionId) return;

    state.breakpoints = state.breakpoints.filter(bp => bp.id !== response.breakpointId);
    renderBreakpointList();
}

function handleError(response) {
    console.error('Error from server:', response.code, response.message);
    // Could show toast notification here
}

// ======================== Event State Application ========================

function applyEventToState(event) {
    switch (event.type) {
        case 'TokenAdded':
            if (!state.marking[event.placeName]) {
                state.marking[event.placeName] = [];
            }
            state.marking[event.placeName].push(event.details.token);
            state.highlightDirty = true;
            break;

        case 'TokenRemoved':
            if (state.marking[event.placeName] && state.marking[event.placeName].length > 0) {
                state.marking[event.placeName].shift();
                // Mark dirty when a place becomes empty (visual change)
                if (state.marking[event.placeName].length === 0) {
                    state.highlightDirty = true;
                }
            }
            break;

        case 'TransitionEnabled':
            if (!state.enabledTransitions.includes(event.transitionName)) {
                state.enabledTransitions.push(event.transitionName);
                state.highlightDirty = true;
            }
            break;

        case 'TransitionStarted':
            state.enabledTransitions = state.enabledTransitions.filter(t => t !== event.transitionName);
            if (!state.inFlightTransitions.includes(event.transitionName)) {
                state.inFlightTransitions.push(event.transitionName);
            }
            state.highlightDirty = true;
            break;

        case 'TransitionCompleted':
        case 'TransitionFailed':
        case 'TransitionTimedOut':
        case 'ActionTimedOut':
            state.inFlightTransitions = state.inFlightTransitions.filter(t => t !== event.transitionName);
            state.highlightDirty = true;
            break;

        case 'MarkingSnapshot':
            state.marking = event.details.marking || {};
            state.highlightDirty = true;
            break;
    }
}

// ======================== Mermaid Diagram ========================

async function renderMermaidDiagram(diagram) {
    const container = document.getElementById('mermaid-diagram');

    // Dispose existing panzoom instance and invalidate SVG cache
    if (state.panzoomInstance) {
        state.panzoomInstance.dispose();
        state.panzoomInstance = null;
    }
    state.svgNodeCache = null;

    if (!diagram) {
        container.innerHTML = '';
        return;
    }

    try {
        // ELK layout is registered in index.html via ES module
        if (window.elkRegistered) {
            console.log('ELK layout available');
        } else {
            console.warn('ELK layout not registered - diagram will use default layout');
        }

        // Initialize Mermaid
        mermaid.initialize({
            startOnLoad: false,
            theme: 'default',
            flowchart: {
                useMaxWidth: true,
                htmlLabels: true
            }
        });

        // Render diagram
        const { svg } = await mermaid.render('mermaid-svg', diagram);
        container.innerHTML = svg;

        // Initialize panzoom on the SVG
        const svgElement = container.querySelector('svg');
        if (svgElement) {
            state.panzoomInstance = panzoom(svgElement, {
                maxZoom: 5,
                minZoom: 0.1,
                bounds: true,
                boundsPadding: 0.1
            });
        }

        // Build SVG node cache for O(1) lookups during highlighting
        buildSvgNodeCache(svgElement);

        // Add click handlers for places and context menu
        container.querySelectorAll('[id*="flowchart"]').forEach(node => {
            node.style.cursor = 'pointer';

            // Left-click: inspect place
            node.addEventListener('click', (e) => {
                // Ctrl+click opens context menu
                if (e.ctrlKey || e.metaKey) {
                    showContextMenu(e, node);
                    return;
                }
                const nodeInfo = parseNodeInfo(node);
                inspectPlace(nodeInfo.name);
            });

            // Right-click: show context menu
            node.addEventListener('contextmenu', (e) => {
                showContextMenu(e, node);
            });
        });

        // Apply initial highlighting
        updateDiagramHighlighting();

    } catch (error) {
        console.error('Failed to render Mermaid diagram:', error);
        container.innerHTML = `<pre class="text-red-500 text-sm">${error.message}</pre>`;
    }
}

/**
 * Builds a cache of SVG nodes and edges, keyed by name and mermaidId.
 * Called once after renderMermaidDiagram() completes. Eliminates all
 * DOM queries from updateDiagramHighlighting().
 *
 * @param {SVGElement} svg - The rendered SVG element
 */
function buildSvgNodeCache(svg) {
    /** @type {Map<string, Element>} */
    const nodesByName = new Map();
    /** @type {Map<string, Element>} */
    const nodesByMermaidId = new Map();
    /** @type {Map<string, Element[]>} */
    const edgesByMermaidId = new Map();

    // Index all .node elements by mermaidId
    svg.querySelectorAll('.node').forEach(node => {
        const match = node.id?.match(/^flowchart-(.+)-\d+$/);
        if (!match) return;
        const mermaidId = match[1];
        nodesByMermaidId.set(mermaidId, node);

        // Resolve authoritative name from structure
        const info = state.netStructure.byMermaidId[mermaidId];
        if (info) {
            nodesByName.set(info.name, node);
        }
    });

    // Also index by fallback sanitization for names not in structure
    state.netStructure.places?.forEach(p => {
        if (!nodesByName.has(p.name) && nodesByMermaidId.has(p.mermaidId)) {
            nodesByName.set(p.name, nodesByMermaidId.get(p.mermaidId));
        }
    });
    state.netStructure.transitions?.forEach(t => {
        if (!nodesByName.has(t.name) && nodesByMermaidId.has(t.mermaidId)) {
            nodesByName.set(t.name, nodesByMermaidId.get(t.mermaidId));
        }
    });

    // Pre-query edges for each mermaidId (all 5 patterns, done once)
    const allMermaidIds = new Set(nodesByMermaidId.keys());
    for (const mermaidId of allMermaidIds) {
        const paths = new Set();

        // Pattern 1: LS-/LE- with flowchart- prefix
        svg.querySelectorAll(`[class*="LS-flowchart-${mermaidId}"], [class*="LE-flowchart-${mermaidId}"]`).forEach(edgeGroup => {
            const path = edgeGroup.querySelector('path');
            if (path) paths.add(path);
        });

        // Pattern 2: LS-/LE- without prefix
        svg.querySelectorAll(`[class*="LS-${mermaidId}"], [class*="LE-${mermaidId}"]`).forEach(edgeGroup => {
            const path = edgeGroup.querySelector('path');
            if (path) paths.add(path);
        });

        // Pattern 3: data-* attributes (ELK layout)
        svg.querySelectorAll(`[data-id*="${mermaidId}"], [data-source*="${mermaidId}"], [data-target*="${mermaidId}"]`).forEach(el => {
            const path = el.tagName === 'path' ? el : el.querySelector('path');
            if (path) paths.add(path);
        });

        // Pattern 4: Edge groups with id
        svg.querySelectorAll(`.edgePath[id*="${mermaidId}"], .edge[id*="${mermaidId}"]`).forEach(edgeGroup => {
            const path = edgeGroup.querySelector('path');
            if (path) paths.add(path);
        });

        // Pattern 5: Mermaid 11 edge labels
        svg.querySelectorAll(`[id*="L-flowchart-${mermaidId}"], [id*="L-${mermaidId}"]`).forEach(edgeGroup => {
            const parent = edgeGroup.closest('.edgePath') || edgeGroup.parentElement;
            const path = parent?.querySelector('path') || edgeGroup.querySelector('path');
            if (path) paths.add(path);
        });

        if (paths.size > 0) {
            edgesByMermaidId.set(mermaidId, [...paths]);
        }
    }

    // Cache all node shapes and edge paths for bulk reset
    const allNodeShapes = [...svg.querySelectorAll('.node rect, .node polygon, .node circle, .node path')];
    const allEdgePaths = [...svg.querySelectorAll('.edgePath path, .flowchart-link, path.path')];

    state.svgNodeCache = { nodesByName, nodesByMermaidId, edgesByMermaidId, allNodeShapes, allEdgePaths };
}

function updateDiagramHighlighting() {
    const cache = state.svgNodeCache;
    if (!cache) return;

    state.highlightDirty = false;

    // Reset all node shapes
    for (const shape of cache.allNodeShapes) {
        shape.style.filter = '';
        shape.style.stroke = '';
        shape.style.strokeWidth = '';
    }

    // Reset all edges
    for (const edge of cache.allEdgePaths) {
        edge.style.stroke = '';
        edge.style.strokeWidth = '';
        edge.style.filter = '';
    }

    // Highlight places with tokens - green glow
    for (const [placeName, tokens] of Object.entries(state.marking)) {
        if (tokens && tokens.length > 0) {
            const node = cache.nodesByName.get(placeName);
            if (node) {
                applyHighlight(node, '#22c55e');
            }
        }
    }

    // Highlight enabled transitions - yellow glow
    for (const transitionName of state.enabledTransitions) {
        const transitionInfo = state.netStructure.transitions?.find(t => t.name === transitionName);
        const transitionMermaidId = transitionInfo?.mermaidId
            || ('t_' + transitionName.replace(/[^a-zA-Z0-9_]/g, '_'));

        const node = cache.nodesByMermaidId.get(transitionMermaidId);
        if (node) {
            applyHighlight(node, '#eab308');
        }

        // Highlight cached edges
        const edges = cache.edgesByMermaidId.get(transitionMermaidId);
        if (edges) {
            for (const path of edges) {
                path.style.stroke = '#eab308';
                path.style.strokeWidth = '3px';
                path.style.filter = 'drop-shadow(0 0 4px #eab308)';
            }
        }
    }

    // Highlight in-flight transitions - orange glow
    for (const transitionName of state.inFlightTransitions) {
        const transitionInfo = state.netStructure.transitions?.find(t => t.name === transitionName);
        const transitionMermaidId = transitionInfo?.mermaidId
            || ('t_' + transitionName.replace(/[^a-zA-Z0-9_]/g, '_'));

        const node = cache.nodesByMermaidId.get(transitionMermaidId);
        if (node) {
            applyHighlight(node, '#f97316');
        }
    }
}

function applyHighlight(node, color) {
    const shape = node.querySelector('rect, polygon, circle, path');
    if (shape) {
        shape.style.stroke = color;
        shape.style.strokeWidth = '3px';
        shape.style.filter = `drop-shadow(0 0 6px ${color})`;
    }
}

/**
 * Finds a diagram node by its authoritative name.
 *
 * Delegates to the SVG node cache for O(1) lookup.
 * Falls back to DOM query if cache is not yet built.
 *
 * @param {SVGElement} svg - The SVG element containing the diagram
 * @param {string} name - The authoritative place or transition name
 * @returns {Element|null} The matching DOM node, or null if not found
 */
function findNodeByName(svg, name) {
    // Use cache if available (O(1) lookup)
    if (state.svgNodeCache) {
        return state.svgNodeCache.nodesByName.get(name) || null;
    }

    // Fallback: DOM query (only before cache is built)
    const place = state.netStructure.places?.find(p => p.name === name);
    const transition = state.netStructure.transitions?.find(t => t.name === name);
    const mermaidId = place?.mermaidId
        || transition?.mermaidId
        || name.replace(/[^a-zA-Z0-9_]/g, '_');

    return svg.querySelector(`[id="flowchart-${mermaidId}-0"]`)
        || svg.querySelector(`[id^="flowchart-${mermaidId}-"]`)
        || svg.querySelector(`.node[id*="-${mermaidId}-"]`);
}

// Expose breakpoint functions globally for onclick handlers
window.toggleBreakpoint = toggleBreakpoint;
window.clearBreakpoint = clearBreakpoint;
window.showTokenDetail = showTokenDetail;
window.showAllTokensModal = showAllTokensModal;

// Debug helper - call from browser console: debugEdgeStructure()
window.debugEdgeStructure = function() {
    const svg = document.querySelector('#mermaid-diagram svg');
    if (!svg) {
        console.log('No SVG found');
        return;
    }

    console.log('=== SVG Edge Structure Debug ===');

    // List all edge-like elements
    console.log('\n--- Edge Paths (.edgePath) ---');
    svg.querySelectorAll('.edgePath').forEach((el, i) => {
        console.log(`  ${i}: id="${el.id}", class="${el.className?.baseVal || el.className}"`);
        el.querySelectorAll('path').forEach((p, j) => {
            console.log(`    path ${j}: class="${p.className?.baseVal || p.className}"`);
        });
    });

    console.log('\n--- Edge elements (.edge) ---');
    svg.querySelectorAll('.edge').forEach((el, i) => {
        console.log(`  ${i}: id="${el.id}", class="${el.className?.baseVal || el.className}"`);
    });

    console.log('\n--- Elements with LS-/LE- classes ---');
    svg.querySelectorAll('[class*="LS-"], [class*="LE-"]').forEach((el, i) => {
        console.log(`  ${i}: tag=${el.tagName}, id="${el.id}", class="${el.className?.baseVal || el.className}"`);
    });

    console.log('\n--- Elements with L- in ID (edge labels) ---');
    svg.querySelectorAll('[id*="L-"]').forEach((el, i) => {
        console.log(`  ${i}: tag=${el.tagName}, id="${el.id}", class="${el.className?.baseVal || el.className}"`);
    });

    console.log('\n--- All path elements ---');
    svg.querySelectorAll('path').forEach((el, i) => {
        const parent = el.parentElement;
        console.log(`  ${i}: parent.id="${parent?.id}", parent.class="${parent?.className?.baseVal || parent?.className}", path.class="${el.className?.baseVal || el.className}"`);
    });

    console.log('\n--- Enabled transitions ---');
    console.log('  ', state.enabledTransitions);

    console.log('\n=== End Debug ===');
};

// ======================== Event Log ========================

/**
 * Creates an event log entry DOM element.
 * Does NOT append to the log - callers handle insertion (single or batch).
 *
 * @param {Object} event - The event data
 * @param {number} index - The event index
 * @returns {HTMLDivElement} The created element
 */
function createEventLogEntry(event, index) {
    const div = document.createElement('div');
    let className = `p-2 bg-gray-700 rounded border-l-4 event-${event.type} cursor-pointer`;
    // Add level-specific CSS class for LogMessage events
    if (event.type === 'LogMessage' && event.details?.level) {
        className += ` level-${event.details.level}`;
    }
    div.className = className;
    div.dataset.eventIndex = String(index);

    const time = new Date(event.timestamp).toLocaleTimeString('en-US', {
        hour12: false,
        hour: '2-digit',
        minute: '2-digit',
        second: '2-digit',
        fractionalSecondDigits: 3
    });

    const name = event.transitionName || event.placeName || '';
    const summary = formatEventSummary(event);
    const fullDetails = formatFullEventDetails(event);

    // Cache searchable text for Phase 4 search optimization
    div.dataset.searchText = `${index} ${time} ${event.type} ${name} ${summary}`.toLowerCase();

    div.innerHTML = `
        <div class="flex items-center justify-between">
            <span class="text-gray-400">${index}</span>
            <span class="text-gray-500">${time}</span>
        </div>
        <div class="font-medium text-gray-200">${event.type}</div>
        ${name ? `<div class="text-gray-400">${name}</div>` : ''}
        ${summary ? `<div class="text-gray-500 text-xs mt-1">${summary}</div>` : ''}
        <div class="event-details hidden mt-2 p-2 bg-gray-800 rounded text-xs overflow-x-auto">
            <pre class="text-gray-300 whitespace-pre-wrap break-all">${fullDetails}</pre>
        </div>
    `;

    return div;
}

function addEventToLog(event, index) {
    const eventLog = document.getElementById('event-log');
    const div = createEventLogEntry(event, index);

    eventLog.appendChild(div);
    eventLog.scrollTop = eventLog.scrollHeight;

    // Update event count
    document.getElementById('event-count').textContent = `${state.events.length} events`;
}

/**
 * Batch-renders event log entries using a DocumentFragment for minimal reflow.
 * Used by reRenderEventLog() and seekToIndex().
 *
 * @param {Array} events - Array of events to render
 * @param {Function} indexFn - Function(event, arrayIndex) returning the event index
 */
function batchRenderEventLog(events, indexFn) {
    const eventLog = document.getElementById('event-log');
    const fragment = document.createDocumentFragment();

    events.forEach((event, i) => {
        if (matchesClientFilter(event)) {
            fragment.appendChild(createEventLogEntry(event, indexFn(event, i)));
        }
    });

    eventLog.innerHTML = '';
    eventLog.appendChild(fragment);
    document.getElementById('event-count').textContent = `${events.length} events`;
}

function formatEventSummary(event) {
    // Quick summary line
    if (!event.details) return '';

    // LogMessage: show [LEVEL] ShortLoggerName: message
    if (event.type === 'LogMessage') {
        const loggerName = event.details.loggerName || '';
        const shortName = loggerName.includes('.') ? loggerName.substring(loggerName.lastIndexOf('.') + 1) : loggerName;
        const level = event.details.level || 'INFO';
        const message = event.details.message || '';
        const parts = [`[${level}] ${shortName}: ${message}`];
        if (event.details.throwable) {
            parts.push(`(${event.details.throwable})`);
        }
        return parts.join(' ');
    }

    const parts = [];

    if (event.details.durationMs !== undefined) {
        parts.push(`${event.details.durationMs}ms`);
    }
    if (event.details.errorMessage) {
        parts.push(event.details.errorMessage);
    }
    if (event.details.consumedTokens?.length) {
        parts.push(`consumed: ${event.details.consumedTokens.length}`);
    }
    if (event.details.producedTokens?.length) {
        parts.push(`produced: ${event.details.producedTokens.length}`);
    }
    if (event.details.token) {
        parts.push(event.details.token.type || 'token');
    }

    return parts.join(' | ');
}

function formatFullEventDetails(event) {
    // Full event details as formatted JSON
    return JSON.stringify(event, null, 2);
}

function clearEventLog() {
    state.events = [];
    document.getElementById('event-log').innerHTML = '';
    document.getElementById('event-count').textContent = '0 events';
}

// ======================== Utility Functions ========================

/**
 * Creates a debounced version of a function.
 * @param {Function} fn - The function to debounce
 * @param {number} delay - Delay in milliseconds
 * @returns {Function}
 */
function debounce(fn, delay) {
    let timer = null;
    return function (...args) {
        if (timer) clearTimeout(timer);
        timer = setTimeout(() => {
            timer = null;
            fn.apply(this, args);
        }, delay);
    };
}

/**
 * Escapes HTML to prevent XSS.
 * @param {string} text - The text to escape
 * @returns {string}
 */
function escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
}

// ======================== Marking Inspector ========================

function updateMarkingInspector() {
    const container = document.getElementById('marking-inspector');

    if (Object.keys(state.marking).length === 0) {
        container.innerHTML = '<div class="text-gray-500">No tokens in marking</div>';
        return;
    }

    container.innerHTML = Object.entries(state.marking)
        .filter(([_, tokens]) => tokens && tokens.length > 0)
        .map(([place, tokens]) => `
            <div class="p-2 bg-gray-700 rounded cursor-pointer hover:bg-gray-600 transition-colors" onclick="inspectPlace('${place}')">
                <div class="flex items-center justify-between">
                    <span class="font-medium text-gray-200">${place}</span>
                    <span class="text-xs bg-blue-600 px-2 py-0.5 rounded-full">${tokens.length}</span>
                </div>
            </div>
        `).join('');

    if (state.highlightDirty) {
        updateDiagramHighlighting();
    }
}

function inspectPlace(placeName) {
    const container = document.getElementById('token-inspector');
    const tokens = state.marking[placeName] || [];

    if (tokens.length === 0) {
        container.innerHTML = `<div class="text-gray-400">No tokens in <strong>${escapeHtml(placeName)}</strong></div>`;
        return;
    }

    const escapedPlaceName = escapeHtml(placeName);

    container.innerHTML = `
        <div class="flex items-center justify-between mb-2">
            <div class="font-medium text-gray-200">${escapedPlaceName} (${tokens.length} tokens)</div>
            ${tokens.length > 1 ? `<button onclick="showAllTokensModal('${escapedPlaceName}')" class="text-xs bg-gray-600 px-2 py-1 rounded hover:bg-gray-500 transition-colors">View All</button>` : ''}
        </div>
        <div class="space-y-2 max-h-48 overflow-y-auto">
            ${tokens.map((token, i) => `
                <div class="p-2 bg-gray-700 rounded text-xs cursor-pointer hover:bg-gray-600 transition-colors" onclick="showTokenDetail('${escapedPlaceName}', ${i})">
                    <div class="flex items-center justify-between">
                        <span class="text-gray-400">#${i + 1} ${escapeHtml(token.type)}</span>
                        <svg class="w-3 h-3 text-gray-500" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15 12a3 3 0 11-6 0 3 3 0 016 0z"/>
                            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M2.458 12C3.732 7.943 7.523 5 12 5c4.478 0 8.268 2.943 9.542 7-1.274 4.057-5.064 7-9.542 7-4.477 0-8.268-2.943-9.542-7z"/>
                        </svg>
                    </div>
                    <div class="text-gray-300 font-mono mt-1 break-all truncate">${escapeHtml(token.value || token.type || '')}</div>
                    ${token.timestamp ? `<div class="text-gray-500 mt-1">${new Date(token.timestamp).toLocaleTimeString()}</div>` : ''}
                </div>
            `).join('')}
        </div>
    `;
}

// ======================== Timeline & Playback ========================

function updateTimelinePosition() {
    const position = document.getElementById('timeline-position');
    position.textContent = `${state.eventIndex} / ${state.totalEvents}`;

    const slider = document.getElementById('timeline-slider');
    slider.max = CONFIG.sliderResolution;
    slider.value = state.totalEvents > 0
        ? (state.eventIndex / state.totalEvents) * CONFIG.sliderResolution
        : 0;
}

function updatePlaybackControls() {
    const pauseBtn = document.getElementById('btn-pause');
    const iconPause = document.getElementById('icon-pause');
    const iconPlay = document.getElementById('icon-play');

    if (state.paused) {
        iconPause.classList.add('hidden');
        iconPlay.classList.remove('hidden');
    } else {
        iconPause.classList.remove('hidden');
        iconPlay.classList.add('hidden');
    }
}

function updateSpeedButtons() {
    document.querySelectorAll('.speed-btn').forEach(btn => {
        const speed = parseFloat(btn.dataset.speed);
        if (speed === state.speed) {
            btn.classList.remove('bg-gray-700');
            btn.classList.add('bg-blue-600');
        } else {
            btn.classList.add('bg-gray-700');
            btn.classList.remove('bg-blue-600');
        }
    });
}

function enableControls(enabled) {
    document.getElementById('btn-restart').disabled = !enabled;
    document.getElementById('btn-step-back').disabled = !enabled;
    document.getElementById('btn-pause').disabled = !enabled;
    document.getElementById('btn-step-forward').disabled = !enabled;
    document.getElementById('btn-run-to-end').disabled = !enabled;
    document.getElementById('timeline-slider').disabled = !enabled;
}

// ======================== UI Helpers ========================

function updateConnectionStatus(connected) {
    const dot = document.getElementById('status-dot');
    const text = document.getElementById('status-text');

    if (connected) {
        dot.classList.remove('bg-red-500');
        dot.classList.add('bg-green-500');
        text.textContent = 'Connected';
    } else {
        dot.classList.remove('bg-green-500');
        dot.classList.add('bg-red-500');
        text.textContent = 'Disconnected';
    }
}

function refreshSessions() {
    send({ type: 'listSessions', limit: 50, activeOnly: false });
}

function subscribeToSession(sessionId, mode = 'live') {
    if (!sessionId) return;

    // Unsubscribe from current session
    if (state.currentSessionId) {
        send({ type: 'unsubscribe', sessionId: state.currentSessionId });
    }

    // Clear UI
    clearEventLog();
    state.marking = {};
    state.enabledTransitions = [];

    // Subscribe to new session
    send({ type: 'subscribe', sessionId, mode, fromIndex: 0 });
}

// ======================== Filter Functions ========================

function sendFilter() {
    if (!state.currentSessionId) return;

    const filter = {
        eventTypes: state.filter.eventTypes.length > 0 ? state.filter.eventTypes : null,
        transitionNames: state.filter.transitionNames.length > 0 ? state.filter.transitionNames : null,
        placeNames: state.filter.placeNames.length > 0 ? state.filter.placeNames : null
    };

    send({
        type: 'filter',
        sessionId: state.currentSessionId,
        filter: filter
    });
}

function applyFilterFromUI() {
    const eventType = document.getElementById('filter-event-type').value;
    const transition = document.getElementById('filter-transition').value.trim();
    const place = document.getElementById('filter-place').value.trim();

    state.filter.eventTypes = eventType ? [eventType] : [];
    state.filter.transitionNames = transition ? [transition] : [];
    state.filter.placeNames = place ? [place] : [];

    sendFilter();
    reRenderEventLog();  // Re-filter displayed events
}

function clearFilter() {
    state.filter = { eventTypes: [], transitionNames: [], placeNames: [] };
    document.getElementById('filter-event-type').value = '';
    document.getElementById('filter-transition').value = '';
    document.getElementById('filter-place').value = '';
    sendFilter();
    reRenderEventLog();  // Re-render to show all events
}

/**
 * Re-renders the event log with current filter applied.
 * Uses batch rendering for minimal reflow.
 */
function reRenderEventLog() {
    const eventsToRender = state.isReplayMode
        ? state.allReplayEvents.slice(0, state.eventIndex)
        : state.events;
    batchRenderEventLog(eventsToRender, (event, i) => i);
}

/**
 * Clears only the event log DOM, preserving the events array.
 */
function clearEventLogDOM() {
    document.getElementById('event-log').innerHTML = '';
}

function updateFilterUI() {
    document.getElementById('filter-event-type').value = state.filter.eventTypes[0] || '';
    document.getElementById('filter-transition').value = state.filter.transitionNames[0] || '';
    document.getElementById('filter-place').value = state.filter.placeNames[0] || '';
}

/**
 * Client-side filter matching for replay mode.
 */
function matchesClientFilter(event) {
    // Event types filter
    if (state.filter.eventTypes.length > 0) {
        if (!state.filter.eventTypes.includes(event.type)) {
            return false;
        }
    }

    // Transition names filter
    if (state.filter.transitionNames.length > 0) {
        if (!event.transitionName || !state.filter.transitionNames.includes(event.transitionName)) {
            return false;
        }
    }

    // Place names filter
    if (state.filter.placeNames.length > 0) {
        if (!event.placeName || !state.filter.placeNames.includes(event.placeName)) {
            return false;
        }
    }

    return true;
}

// ======================== Autocomplete Functions ========================

/**
 * Updates the datalist options for transition and place autocomplete.
 *
 * Uses the server-provided net structure as the primary source of truth,
 * supplemented by data from events and the diagram for completeness.
 */
function updateAutocompleteOptions() {
    const transitions = new Set();
    const places = new Set();

    // Primary source: use structure from server (authoritative names)
    if (state.netStructure.transitions) {
        state.netStructure.transitions.forEach(t => transitions.add(t.name));
    }
    if (state.netStructure.places) {
        state.netStructure.places.forEach(p => places.add(p.name));
    }

    // Secondary source: collect from events (may have names not yet in structure)
    const eventsToScan = state.isReplayMode ? state.allReplayEvents : state.events;
    eventsToScan.forEach(e => {
        if (e.transitionName) transitions.add(e.transitionName);
        if (e.placeName) places.add(e.placeName);
    });

    // Tertiary source: enabled transitions and current marking
    state.enabledTransitions.forEach(t => transitions.add(t));
    Object.keys(state.marking).forEach(p => places.add(p));

    // Fallback: parse SVG for any nodes not in structure (backward compatibility)
    if (state.netStructure.places.length === 0 && state.netStructure.transitions.length === 0) {
        const svg = document.querySelector('#mermaid-diagram svg');
        if (svg) {
            svg.querySelectorAll('.node').forEach(node => {
                const nodeId = node.id || '';
                const match = nodeId.match(/^flowchart-(.+)-\d+$/);
                if (match) {
                    const mermaidId = match[1];
                    if (mermaidId.startsWith('t_')) {
                        transitions.add(mermaidId.substring(2));
                    } else {
                        places.add(mermaidId);
                    }
                }
            });
        }
    }

    // Update transition datalist
    document.getElementById('transition-options').innerHTML =
        [...transitions].sort().map(t => `<option value="${t}">`).join('');

    // Update place datalist
    document.getElementById('place-options').innerHTML =
        [...places].sort().map(p => `<option value="${p}">`).join('');
}

// ======================== Search Functions ========================

function performSearch(term) {
    state.searchTerm = term.toLowerCase();
    state.searchMatches = [];
    state.currentMatchIndex = -1;

    // Clear previous highlights
    document.querySelectorAll('#event-log > div').forEach(el => {
        el.classList.remove('search-match', 'search-current');
    });

    if (!state.searchTerm) {
        updateSearchDisplay();
        return;
    }

    // Find matching events using cached search text (no DOM text extraction)
    const eventElements = document.querySelectorAll('#event-log > div');
    eventElements.forEach((el, index) => {
        const text = el.dataset.searchText || el.textContent.toLowerCase();
        if (text.includes(state.searchTerm)) {
            state.searchMatches.push(index);
            el.classList.add('search-match');
        }
    });

    updateSearchDisplay();

    // Navigate to first match
    if (state.searchMatches.length > 0) {
        navigateToMatch(0);
    }
}

function navigateToMatch(matchIndex) {
    if (state.searchMatches.length === 0) return;

    // Wrap around
    if (matchIndex < 0) {
        matchIndex = state.searchMatches.length - 1;
    } else if (matchIndex >= state.searchMatches.length) {
        matchIndex = 0;
    }

    // Remove current highlight from previous match
    if (state.currentMatchIndex >= 0 && state.currentMatchIndex < state.searchMatches.length) {
        const prevIndex = state.searchMatches[state.currentMatchIndex];
        const prevEl = document.querySelectorAll('#event-log > div')[prevIndex];
        if (prevEl) {
            prevEl.classList.remove('search-current');
        }
    }

    state.currentMatchIndex = matchIndex;
    const eventIndex = state.searchMatches[matchIndex];
    const eventElements = document.querySelectorAll('#event-log > div');
    const el = eventElements[eventIndex];

    if (el) {
        el.classList.add('search-current');
        el.scrollIntoView({ behavior: 'smooth', block: 'center' });
    }

    updateSearchDisplay();
}

function navigateSearchPrev() {
    navigateToMatch(state.currentMatchIndex - 1);
}

function navigateSearchNext() {
    navigateToMatch(state.currentMatchIndex + 1);
}

function clearSearch() {
    state.searchTerm = '';
    state.searchMatches = [];
    state.currentMatchIndex = -1;

    document.getElementById('search-input').value = '';
    document.querySelectorAll('#event-log > div').forEach(el => {
        el.classList.remove('search-match', 'search-current');
    });

    updateSearchDisplay();
}

function updateSearchDisplay() {
    const resultsEl = document.getElementById('search-results');
    const prevBtn = document.getElementById('search-prev');
    const nextBtn = document.getElementById('search-next');

    if (state.searchMatches.length === 0) {
        resultsEl.textContent = state.searchTerm ? '0/0' : '-';
        prevBtn.disabled = true;
        nextBtn.disabled = true;
    } else {
        resultsEl.textContent = `${state.currentMatchIndex + 1}/${state.searchMatches.length}`;
        prevBtn.disabled = false;
        nextBtn.disabled = false;
    }
}

// ======================== Breakpoint Functions ========================

/**
 * Checks if an event matches any enabled breakpoint (client-side, for replay mode).
 * @param {Object} event - The event to check
 * @returns {Object|null} The matching breakpoint, or null
 */
function checkClientBreakpoints(event) {
    for (const bp of state.breakpoints) {
        if (!bp.enabled) continue;

        const eventType = event.type;
        const matchesTarget = (bpTarget, name) => !bpTarget || bpTarget === name;

        switch (bp.type) {
            case 'TRANSITION_ENABLED':
                if (eventType === 'TransitionEnabled' && matchesTarget(bp.target, event.transitionName)) return bp;
                break;
            case 'TRANSITION_START':
                if (eventType === 'TransitionStarted' && matchesTarget(bp.target, event.transitionName)) return bp;
                break;
            case 'TRANSITION_COMPLETE':
                if (eventType === 'TransitionCompleted' && matchesTarget(bp.target, event.transitionName)) return bp;
                break;
            case 'TRANSITION_FAIL':
                if (eventType === 'TransitionFailed' && matchesTarget(bp.target, event.transitionName)) return bp;
                break;
            case 'TOKEN_ADDED':
                if (eventType === 'TokenAdded' && matchesTarget(bp.target, event.placeName)) return bp;
                break;
            case 'TOKEN_REMOVED':
                if (eventType === 'TokenRemoved' && matchesTarget(bp.target, event.placeName)) return bp;
                break;
        }
    }
    return null;
}

function addBreakpoint(type, target) {
    if (!state.currentSessionId) return;

    const bp = {
        id: 'bp_' + Date.now(),
        type: type,
        target: target || null,
        enabled: true
    };

    if (state.isReplayMode) {
        // In replay mode, manage breakpoints locally
        state.breakpoints.push(bp);
        renderBreakpointList();
    } else {
        send({
            type: 'setBreakpoint',
            sessionId: state.currentSessionId,
            breakpoint: bp
        });
    }
}

function toggleBreakpoint(breakpointId) {
    const bp = state.breakpoints.find(b => b.id === breakpointId);
    if (!bp || !state.currentSessionId) return;

    // Toggle enabled state
    const updatedBp = { ...bp, enabled: !bp.enabled };

    // Update local state immediately
    const index = state.breakpoints.findIndex(b => b.id === breakpointId);
    if (index >= 0) {
        state.breakpoints[index] = updatedBp;
        renderBreakpointList();
    }

    if (!state.isReplayMode) {
        send({
            type: 'setBreakpoint',
            sessionId: state.currentSessionId,
            breakpoint: updatedBp
        });
    }
}

function clearBreakpoint(breakpointId) {
    if (!state.currentSessionId) return;

    if (state.isReplayMode) {
        // In replay mode, manage breakpoints locally
        state.breakpoints = state.breakpoints.filter(bp => bp.id !== breakpointId);
        renderBreakpointList();
    } else {
        send({
            type: 'clearBreakpoint',
            sessionId: state.currentSessionId,
            breakpointId: breakpointId
        });
    }
}

function listBreakpoints() {
    if (!state.currentSessionId) return;

    send({
        type: 'listBreakpoints',
        sessionId: state.currentSessionId
    });
}

function renderBreakpointList() {
    const container = document.getElementById('breakpoint-list');

    if (state.breakpoints.length === 0) {
        container.innerHTML = '<div class="text-gray-500">No breakpoints</div>';
        return;
    }

    container.innerHTML = state.breakpoints.map(bp => `
        <div class="flex items-center gap-2 p-2 bg-gray-700 rounded" data-bp-id="${bp.id}">
            <input type="checkbox" ${bp.enabled ? 'checked' : ''}
                   onchange="toggleBreakpoint('${bp.id}')"
                   class="rounded border-gray-500">
            <div class="flex-1 overflow-hidden">
                <div class="font-medium text-gray-200 truncate">${formatBreakpointType(bp.type)}</div>
                ${bp.target ? `<div class="text-xs text-gray-400 truncate">${bp.target}</div>` : ''}
            </div>
            <button onclick="clearBreakpoint('${bp.id}')"
                    class="text-gray-400 hover:text-red-400 transition-colors">
                <svg class="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                    <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M6 18L18 6M6 6l12 12"/>
                </svg>
            </button>
        </div>
    `).join('');
}

function formatBreakpointType(type) {
    const labels = {
        'TRANSITION_START': 'Trans. Start',
        'TRANSITION_COMPLETE': 'Trans. Complete',
        'TRANSITION_ENABLED': 'Trans. Enabled',
        'TRANSITION_FAIL': 'Trans. Fail',
        'TOKEN_ADDED': 'Token Added',
        'TOKEN_REMOVED': 'Token Removed'
    };
    return labels[type] || type;
}

function highlightBreakpointInList(breakpointId) {
    const el = document.querySelector(`[data-bp-id="${breakpointId}"]`);
    if (el) {
        el.classList.add('ring-2', 'ring-yellow-500');
        setTimeout(() => {
            el.classList.remove('ring-2', 'ring-yellow-500');
        }, 2000);
    }
}

function showBreakpointNotification(breakpointId, event) {
    // Flash the pause button to indicate breakpoint hit
    const pauseBtn = document.getElementById('btn-pause');
    pauseBtn.classList.add('bg-yellow-500');
    setTimeout(() => {
        pauseBtn.classList.remove('bg-yellow-500');
        pauseBtn.classList.add('bg-green-700');
    }, 1000);

    console.log(`Breakpoint ${breakpointId} hit on ${event.type}: ${event.transitionName || event.placeName || ''}`);
}

function showBreakpointForm() {
    document.getElementById('breakpoint-form').classList.remove('hidden');
    document.getElementById('bp-target').focus();
}

function hideBreakpointForm() {
    document.getElementById('breakpoint-form').classList.add('hidden');
    document.getElementById('bp-type').value = 'TRANSITION_START';
    document.getElementById('bp-target').value = '';
}

function saveBreakpointFromForm() {
    const type = document.getElementById('bp-type').value;
    const target = document.getElementById('bp-target').value.trim();
    addBreakpoint(type, target);
    hideBreakpointForm();
}

// ======================== Context Menu Functions ========================

// State for context menu
let contextMenuTarget = null;

/**
 * Parses node information from a Mermaid diagram node element.
 *
 * Uses the server-provided net structure for authoritative name lookup.
 * Falls back to heuristic parsing if structure is not available.
 *
 * @param {Element} node - The SVG node element
 * @returns {{name: string, isTransition: boolean}}
 */
function parseNodeInfo(node) {
    const nodeId = node.id || '';

    // Extract Mermaid's sanitized ID from SVG node ID (format: flowchart-{mermaidId}-{number})
    const match = nodeId.match(/^flowchart-(.+)-\d+$/);
    if (!match) {
        return { name: node.textContent?.trim() || '', isTransition: false };
    }

    const mermaidId = match[1];

    // Look up in structure (authoritative source from server)
    const info = state.netStructure.byMermaidId[mermaidId];
    if (info) {
        return { name: info.name, isTransition: info.isTransition };
    }

    // Fallback: old heuristic (for backward compatibility or if structure unavailable)
    if (mermaidId.startsWith('t_')) {
        return { name: mermaidId.substring(2), isTransition: true };
    }
    return { name: mermaidId, isTransition: false };
}

/**
 * Shows the context menu at the specified position.
 * @param {MouseEvent} event - The mouse event
 * @param {Element} node - The diagram node element
 */
function showContextMenu(event, node) {
    event.preventDefault();
    event.stopPropagation();

    const menu = document.getElementById('diagram-context-menu');
    const nodeInfo = parseNodeInfo(node);
    contextMenuTarget = nodeInfo;

    // Set header
    const header = document.getElementById('ctx-menu-header');
    header.textContent = nodeInfo.name;
    header.title = nodeInfo.name;

    // Show appropriate breakpoint options
    const placeOptions = document.getElementById('ctx-bp-place-options');
    const transitionOptions = document.getElementById('ctx-bp-transition-options');

    if (nodeInfo.isTransition) {
        placeOptions.classList.add('hidden');
        transitionOptions.classList.remove('hidden');
    } else {
        placeOptions.classList.remove('hidden');
        transitionOptions.classList.add('hidden');
    }

    // Position menu
    const x = event.clientX;
    const y = event.clientY;

    menu.style.left = `${x}px`;
    menu.style.top = `${y}px`;
    menu.classList.remove('hidden');

    // Adjust position if menu goes off screen
    requestAnimationFrame(() => {
        const rect = menu.getBoundingClientRect();
        if (rect.right > window.innerWidth) {
            menu.style.left = `${x - rect.width}px`;
        }
        if (rect.bottom > window.innerHeight) {
            menu.style.top = `${y - rect.height}px`;
        }
    });
}

/**
 * Hides the context menu.
 */
function hideContextMenu() {
    const menu = document.getElementById('diagram-context-menu');
    menu.classList.add('hidden');
    contextMenuTarget = null;
}

/**
 * Handles breakpoint creation from context menu.
 * @param {string} type - The breakpoint type
 */
function handleContextMenuBreakpoint(type) {
    if (contextMenuTarget && contextMenuTarget.name) {
        addBreakpoint(type, contextMenuTarget.name);
    }
    hideContextMenu();
}

/**
 * Handles inspect action from context menu.
 */
function handleContextMenuInspect() {
    if (contextMenuTarget && contextMenuTarget.name) {
        inspectPlace(contextMenuTarget.name);
    }
    hideContextMenu();
}

// ======================== Value Modal Functions ========================

// Store current modal value for copy functionality
let currentModalValue = '';

/**
 * Applies syntax highlighting to JSON.
 * @param {string} json - The JSON string to highlight
 * @returns {string} - HTML with syntax highlighting
 */
function syntaxHighlightJson(json) {
    // Escape HTML first
    const escaped = escapeHtml(json);
    // Apply syntax highlighting
    return escaped.replace(
        /("(\\u[a-zA-Z0-9]{4}|\\[^u]|[^\\"])*"(\s*:)?|\b(true|false|null)\b|-?\d+(?:\.\d*)?(?:[eE][+\-]?\d+)?)/g,
        (match) => {
            let cls = 'json-number';
            if (/^"/.test(match)) {
                if (/:$/.test(match)) {
                    cls = 'json-key';
                } else {
                    cls = 'json-string';
                }
            } else if (/true|false/.test(match)) {
                cls = 'json-boolean';
            } else if (/null/.test(match)) {
                cls = 'json-null';
            }
            return `<span class="${cls}">${match}</span>`;
        }
    );
}

/**
 * Shows a single token's details in the modal.
 * @param {string} placeName - The place name
 * @param {number} tokenIndex - The token index (0-based)
 */
function showTokenDetail(placeName, tokenIndex) {
    const tokens = state.marking[placeName] || [];
    if (tokenIndex < 0 || tokenIndex >= tokens.length) return;

    const token = tokens[tokenIndex];
    const modal = document.getElementById('value-modal');
    const title = document.getElementById('modal-title');
    const subtitle = document.getElementById('modal-subtitle');
    const jsonContainer = document.getElementById('modal-json');

    title.textContent = `Token #${tokenIndex + 1}`;
    subtitle.textContent = `${placeName} - ${token.type}`;

    // Show full value if available, otherwise fall back to full token JSON
    const displayValue = token.value || '';
    // Try to parse and pretty-print if it looks like JSON
    let formatted;
    try {
        const parsed = JSON.parse(displayValue);
        formatted = JSON.stringify(parsed, null, 2);
    } catch {
        formatted = displayValue;
    }

    currentModalValue = formatted;
    jsonContainer.innerHTML = syntaxHighlightJson(formatted);

    modal.classList.remove('hidden');
}

/**
 * Shows all tokens for a place in the modal.
 * @param {string} placeName - The place name
 */
function showAllTokensModal(placeName) {
    const tokens = state.marking[placeName] || [];
    if (tokens.length === 0) return;

    const modal = document.getElementById('value-modal');
    const title = document.getElementById('modal-title');
    const subtitle = document.getElementById('modal-subtitle');
    const jsonContainer = document.getElementById('modal-json');

    title.textContent = `All Tokens`;
    subtitle.textContent = `${placeName} - ${tokens.length} token(s)`;

    // Show tokens with full values
    const displayTokens = tokens.map(t => ({
        type: t.type,
        value: t.value,
        timestamp: t.timestamp
    }));
    currentModalValue = JSON.stringify(displayTokens, null, 2);
    jsonContainer.innerHTML = syntaxHighlightJson(currentModalValue);

    modal.classList.remove('hidden');
}

/**
 * Closes the value modal.
 */
function closeValueModal() {
    const modal = document.getElementById('value-modal');
    modal.classList.add('hidden');
    currentModalValue = '';
}

/**
 * Copies the current modal value to clipboard.
 */
async function copyModalValue() {
    if (!currentModalValue) return;

    try {
        await navigator.clipboard.writeText(currentModalValue);
        // Visual feedback
        const copyBtn = document.getElementById('modal-copy');
        const originalText = copyBtn.textContent;
        copyBtn.textContent = 'Copied!';
        copyBtn.classList.remove('bg-blue-600', 'hover:bg-blue-700');
        copyBtn.classList.add('bg-green-600');
        setTimeout(() => {
            copyBtn.textContent = originalText;
            copyBtn.classList.remove('bg-green-600');
            copyBtn.classList.add('bg-blue-600', 'hover:bg-blue-700');
        }, 1500);
    } catch (err) {
        console.error('Failed to copy to clipboard:', err);
    }
}

// ======================== Event Listeners ========================

document.addEventListener('DOMContentLoaded', () => {
    // Connect WebSocket
    connect();

    // Session select
    document.getElementById('session-select').addEventListener('change', (e) => {
        const mode = document.getElementById('mode-select').value;
        subscribeToSession(e.target.value, mode);
    });

    // Mode select
    document.getElementById('mode-select').addEventListener('change', (e) => {
        const sessionId = document.getElementById('session-select').value;
        if (sessionId) {
            subscribeToSession(sessionId, e.target.value);
        }
    });

    // Refresh sessions
    document.getElementById('refresh-sessions').addEventListener('click', refreshSessions);

    // Reset zoom
    document.getElementById('reset-zoom').addEventListener('click', () => {
        if (state.panzoomInstance) {
            state.panzoomInstance.moveTo(0, 0);
            state.panzoomInstance.zoomAbs(0, 0, 1);
        }
    });

    // Clear events
    document.getElementById('clear-events').addEventListener('click', clearEventLog);

    // Delegated click handler for event log entries (replaces per-entry listeners)
    document.getElementById('event-log').addEventListener('click', (e) => {
        const entry = e.target.closest('[data-event-index]');
        if (!entry) return;
        const details = entry.querySelector('.event-details');
        if (details) details.classList.toggle('hidden');
    });

    // Filter controls
    document.getElementById('apply-filter').addEventListener('click', applyFilterFromUI);
    document.getElementById('clear-filter').addEventListener('click', clearFilter);

    // Apply filter on Enter key in filter inputs
    ['filter-transition', 'filter-place'].forEach(id => {
        document.getElementById(id).addEventListener('keypress', (e) => {
            if (e.key === 'Enter') {
                applyFilterFromUI();
            }
        });
    });

    // Search controls - debounced to avoid searching on every keystroke
    const debouncedSearch = debounce((value) => {
        performSearch(value);
    }, 200);
    document.getElementById('search-input').addEventListener('input', (e) => {
        debouncedSearch(e.target.value);
    });
    document.getElementById('search-input').addEventListener('keypress', (e) => {
        if (e.key === 'Enter') {
            if (e.shiftKey) {
                navigateSearchPrev();
            } else {
                navigateSearchNext();
            }
        }
    });
    document.getElementById('search-prev').addEventListener('click', navigateSearchPrev);
    document.getElementById('search-next').addEventListener('click', navigateSearchNext);
    document.getElementById('search-clear').addEventListener('click', clearSearch);

    // Breakpoint controls
    document.getElementById('add-breakpoint').addEventListener('click', showBreakpointForm);
    document.getElementById('bp-save').addEventListener('click', saveBreakpointFromForm);
    document.getElementById('bp-cancel').addEventListener('click', hideBreakpointForm);
    document.getElementById('bp-target').addEventListener('keypress', (e) => {
        if (e.key === 'Enter') {
            saveBreakpointFromForm();
        }
    });

    // Switch datalist based on breakpoint type (transition vs place)
    document.getElementById('bp-type').addEventListener('change', (e) => {
        const isPlaceType = e.target.value.startsWith('TOKEN_');
        const input = document.getElementById('bp-target');
        input.setAttribute('list', isPlaceType ? 'place-options' : 'transition-options');
        input.placeholder = isPlaceType ? 'Place name...' : 'Transition name...';
    });

    // Debugger controls
    document.getElementById('btn-restart').addEventListener('click', () => {
        if (state.isReplayMode) {
            stopPlayback();
            state.paused = true;
            seekToIndex(0);
            updatePlaybackControls();
        }
    });

    document.getElementById('btn-step-back').addEventListener('click', () => {
        if (state.isReplayMode && state.eventIndex > 0) {
            stopPlayback();
            state.paused = true;
            seekToIndex(state.eventIndex - 1);
            updatePlaybackControls();
        } else if (state.currentSessionId && !state.isReplayMode) {
            send({ type: 'stepBackward', sessionId: state.currentSessionId });
        }
    });

    document.getElementById('btn-pause').addEventListener('click', () => {
        if (state.isReplayMode) {
            // Frontend-controlled playback for replay mode
            if (state.paused) {
                state.paused = false;
                startPlayback();
            } else {
                state.paused = true;
                stopPlayback();
            }
            updatePlaybackControls();
        } else if (state.currentSessionId) {
            // Live mode - send to server (existing behavior)
            if (state.paused) {
                send({ type: 'resume', sessionId: state.currentSessionId });
            } else {
                send({ type: 'pause', sessionId: state.currentSessionId });
            }
        }
    });

    document.getElementById('btn-step-forward').addEventListener('click', () => {
        if (state.isReplayMode && state.eventIndex < state.allReplayEvents.length) {
            stopPlayback();
            state.paused = true;
            const event = state.allReplayEvents[state.eventIndex];
            applyEventToState(event);
            if (matchesClientFilter(event)) {
                addEventToLog(event, state.eventIndex);
            }
            state.eventIndex++;
            updateMarkingInspector();
            updateTimelinePosition();
            updatePlaybackControls();
        } else if (state.currentSessionId && !state.isReplayMode) {
            send({ type: 'stepForward', sessionId: state.currentSessionId });
        }
    });

    document.getElementById('btn-run-to-end').addEventListener('click', () => {
        if (state.isReplayMode) {
            stopPlayback();
            state.paused = true;
            seekToIndex(state.allReplayEvents.length);
            updatePlaybackControls();
        }
    });

    // Speed buttons
    document.querySelectorAll('.speed-btn').forEach(btn => {
        btn.addEventListener('click', () => {
            const speed = parseFloat(btn.dataset.speed);
            state.speed = speed;
            updateSpeedButtons();
            if (state.isReplayMode && !state.paused) {
                // Restart timer with new speed
                stopPlayback();
                startPlayback();
            } else if (state.currentSessionId && !state.isReplayMode) {
                send({ type: 'playbackSpeed', sessionId: state.currentSessionId, speed });
            }
        });
    });

    // Timeline slider - debounce seek in replay mode for smooth dragging
    const debouncedSeek = debounce((targetIndex) => {
        seekToIndex(targetIndex);
    }, 50);

    document.getElementById('timeline-slider').addEventListener('input', (e) => {
        const sliderValue = parseFloat(e.target.value);
        if (state.isReplayMode) {
            const targetIndex = state.totalEvents > 0
                ? Math.round((sliderValue / CONFIG.sliderResolution) * state.totalEvents)
                : 0;
            // Update position text immediately for responsiveness
            document.getElementById('timeline-position').textContent =
                `${targetIndex} / ${state.totalEvents}`;
            debouncedSeek(targetIndex);
        } else if (state.currentSessionId && state.events[0]?.timestamp) {
            const targetIndex = state.totalEvents > 0
                ? Math.round((sliderValue / CONFIG.sliderResolution) * state.events.length)
                : 0;
            const targetEvent = state.events[targetIndex];
            if (targetEvent) {
                send({
                    type: 'seek',
                    sessionId: state.currentSessionId,
                    timestamp: targetEvent.timestamp
                });
            }
        }
    });

    // Context menu event listeners
    document.getElementById('ctx-menu-inspect').addEventListener('click', handleContextMenuInspect);

    // Context menu breakpoint options
    document.querySelectorAll('.ctx-bp-option').forEach(option => {
        option.addEventListener('click', () => {
            const bpType = option.dataset.bpType;
            handleContextMenuBreakpoint(bpType);
        });
    });

    // Hide context menu on click outside
    document.addEventListener('click', (e) => {
        const menu = document.getElementById('diagram-context-menu');
        if (!menu.contains(e.target)) {
            hideContextMenu();
        }
    });

    // Hide context menu on escape key
    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') {
            hideContextMenu();
            closeValueModal();
        }
    });

    // Modal event listeners
    document.getElementById('modal-close').addEventListener('click', closeValueModal);
    document.getElementById('modal-copy').addEventListener('click', copyModalValue);

    // Close modal on background click
    document.getElementById('value-modal').addEventListener('click', (e) => {
        if (e.target.id === 'value-modal') {
            closeValueModal();
        }
    });
});
