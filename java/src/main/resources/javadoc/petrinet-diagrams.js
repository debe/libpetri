// Petri Net Diagram Viewer
// Provides: zoom/pan and fullscreen for pre-rendered SVG diagrams

(function() {
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', enhanceDiagrams);
  } else {
    enhanceDiagrams();
  }
})();

function enhanceDiagrams() {
  document.querySelectorAll('.petrinet-diagram').forEach(function(diagram) {
    var container = diagram.querySelector('.diagram-container');
    var svg = container ? container.querySelector('svg') : null;
    if (!svg) return;

    var scale = 1, panX = 0, panY = 0;
    var isPanning = false, startX, startY;

    // Zoom indicator
    var indicator = document.createElement('div');
    indicator.className = 'zoom-indicator';
    indicator.textContent = '100%';
    container.appendChild(indicator);
    var hideTimeout;

    function applyTransform() {
      svg.style.transform = 'translate(' + panX + 'px, ' + panY + 'px) scale(' + scale + ')';
      svg.style.transformOrigin = 'center center';
    }

    function showZoom() {
      indicator.textContent = Math.round(scale * 100) + '%';
      indicator.classList.add('visible');
      clearTimeout(hideTimeout);
      hideTimeout = setTimeout(function() { indicator.classList.remove('visible'); }, 1000);
    }

    // Ctrl+wheel to zoom
    container.addEventListener('wheel', function(e) {
      if (!e.ctrlKey) return;
      e.preventDefault();
      var delta = e.deltaY > 0 ? 0.9 : 1.1;
      var newScale = Math.max(0.1, Math.min(5, scale * delta));
      var rect = container.getBoundingClientRect();
      var mouseX = e.clientX - rect.left - rect.width / 2;
      var mouseY = e.clientY - rect.top - rect.height / 2;
      panX = mouseX - (mouseX - panX) * (newScale / scale);
      panY = mouseY - (mouseY - panY) * (newScale / scale);
      scale = newScale;
      applyTransform();
      showZoom();
    }, { passive: false });

    // Drag to pan
    container.addEventListener('mousedown', function(e) {
      if (e.button !== 0) return;
      isPanning = true;
      startX = e.clientX - panX;
      startY = e.clientY - panY;
      container.style.cursor = 'grabbing';
    });

    document.addEventListener('mousemove', function(e) {
      if (!isPanning) return;
      panX = e.clientX - startX;
      panY = e.clientY - startY;
      applyTransform();
    });

    document.addEventListener('mouseup', function() {
      if (isPanning) {
        isPanning = false;
        container.style.cursor = 'grab';
      }
    });

    // Reset button
    var resetBtn = diagram.querySelector('.btn-reset');
    if (resetBtn) {
      resetBtn.addEventListener('click', function() {
        scale = 1; panX = 0; panY = 0;
        applyTransform();
        showZoom();
      });
    }

    container.style.cursor = 'grab';
  });
}

// Fullscreen toggle (namespaced to avoid global pollution)
window.PetriNetDiagrams = window.PetriNetDiagrams || {};
PetriNetDiagrams.toggleFullscreen = function(btn) {
  var diagram = btn.closest('.petrinet-diagram');
  diagram.classList.toggle('diagram-fullscreen');
  btn.textContent = diagram.classList.contains('diagram-fullscreen') ? 'Exit' : 'Fullscreen';
  document.body.style.overflow = diagram.classList.contains('diagram-fullscreen') ? 'hidden' : '';
};

// ESC to exit fullscreen
document.addEventListener('keydown', function(e) {
  if (e.key === 'Escape') {
    var fs = document.querySelector('.diagram-fullscreen');
    if (fs) {
      var btn = fs.querySelector('.btn-fullscreen');
      if (btn) btn.click();
    }
  }
});
