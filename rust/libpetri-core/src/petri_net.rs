use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::action::BoxedAction;
use crate::compose::ComposeBindingsBuilder;
use crate::fusion::{FusionSet, FusionSetBuilder};
use crate::instance::Instance;
use crate::place::PlaceRef;
use crate::rewriter;
use crate::subnet_def::SubnetDef;
use crate::transition::{Transition, rebuild_with_action};

/// Immutable definition of a Time Petri Net structure.
///
/// A PetriNet is a reusable definition that can be executed multiple times
/// with different initial markings. Places are auto-collected from transitions.
///
/// Place storage is a `Vec<PlaceRef>` (rather than a `HashSet`) so that
/// iteration order matches the order in which the builder discovered each
/// distinct place — the cross-language byte-parity contract on the DOT
/// exporter (per `[EXP-014]`, see `scripts/cross-lang-dot-parity.sh`)
/// requires this stable order. Membership lookups remain available via
/// `places().contains(...)` (linear scan over a small `Vec` is cheap for
/// every realistic net size and never hot in practice).
#[derive(Debug, Clone)]
pub struct PetriNet {
    name: Arc<str>,
    places: Vec<PlaceRef>,
    transitions: Vec<Transition>,
    /// MOD-026: node name -> owning subnet name, for cluster-aware DOT
    /// export. Recorded by [`PetriNetBuilder::compose_direct`]; empty for
    /// every net not built via direct composition.
    ///
    /// A plain `HashMap` is correct here even though the cross-language
    /// byte-parity contract demands deterministic DOT output: the exporter
    /// iterates over the net's nodes (themselves order-preserving) and
    /// *looks up* membership, so the map's own iteration order never
    /// reaches the rendered DOT — no `IndexMap` is needed.
    subnet_membership: HashMap<Arc<str>, Arc<str>>,
}

impl PetriNet {
    /// Returns the net name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns all places in the net, in builder-insertion order.
    pub fn places(&self) -> &[PlaceRef] {
        &self.places
    }

    /// Returns the transitions in the net.
    pub fn transitions(&self) -> &[Transition] {
        &self.transitions
    }

    /// Subnet-membership metadata per **MOD-026**: maps each node name
    /// (place or transition) contributed by exactly one directly-composed
    /// subnet to that subnet's name. Shared places contributed by two or
    /// more subnets, and every node of a net not built via
    /// [`PetriNetBuilder::compose_direct`], are absent. Never `None` —
    /// empty when there is no metadata. The DOT exporter renders `subgraph
    /// cluster_*` blocks from this map.
    pub fn subnet_membership(&self) -> &HashMap<Arc<str>, Arc<str>> {
        &self.subnet_membership
    }

    /// Creates a new PetriNet with actions bound to transitions by name.
    /// Transitions not in the map keep their existing action.
    pub fn bind_actions(
        &self,
        bindings: &std::collections::HashMap<String, BoxedAction>,
    ) -> PetriNet {
        self.bind_actions_with_resolver(|name| bindings.get(name).cloned())
    }

    /// Creates a new PetriNet with actions bound via a resolver function.
    /// If the resolver returns None, the transition keeps its existing action.
    pub fn bind_actions_with_resolver(
        &self,
        resolver: impl Fn(&str) -> Option<BoxedAction>,
    ) -> PetriNet {
        let transitions: Vec<Transition> = self
            .transitions
            .iter()
            .map(|t: &Transition| {
                if let Some(action) = resolver(t.name()) {
                    rebuild_with_action(t, action)
                } else {
                    t.clone()
                }
            })
            .collect();

        // MOD-026: bind_actions rebuilds transitions but preserves their
        // names, so name-keyed membership metadata survives a session bind
        // unchanged — clone it through.
        PetriNet {
            name: Arc::clone(&self.name),
            places: self.places.clone(),
            transitions,
            subnet_membership: self.subnet_membership.clone(),
        }
    }

    /// Creates a new PetriNetBuilder.
    pub fn builder(name: impl Into<Arc<str>>) -> PetriNetBuilder {
        PetriNetBuilder::new(name)
    }
}

/// Builder for constructing PetriNet instances.
///
/// Place storage is an order-preserving dedup'd `Vec` plus a parallel
/// `HashSet` for O(1) membership — see [`PetriNet`] docs for the
/// cross-language byte-parity rationale.
pub struct PetriNetBuilder {
    name: Arc<str>,
    places: Vec<PlaceRef>,
    place_index: HashSet<PlaceRef>,
    transitions: Vec<Transition>,
    fusion_sets: Vec<FusionSet>,
    /// MOD-026: node name -> set of subnet names that contributed it via
    /// [`PetriNetBuilder::compose_direct`]. Resolved to single-owner
    /// membership at [`PetriNetBuilder::build`].
    subnet_contributions: HashMap<Arc<str>, HashSet<Arc<str>>>,
}

impl PetriNetBuilder {
    pub fn new(name: impl Into<Arc<str>>) -> Self {
        Self {
            name: name.into(),
            places: Vec::new(),
            place_index: HashSet::new(),
            transitions: Vec::new(),
            fusion_sets: Vec::new(),
            subnet_contributions: HashMap::new(),
        }
    }

    /// Inserts a place if it was not previously present, preserving the
    /// builder's insertion order. Centralised so every auto-collection
    /// site (transition input/output/inhibitor/read/reset) goes through
    /// the same dedup path.
    fn insert_place(&mut self, place: PlaceRef) {
        if self.place_index.insert(place.clone()) {
            self.places.push(place);
        }
    }

    /// Add an explicit place.
    pub fn place(mut self, place: PlaceRef) -> Self {
        self.insert_place(place);
        self
    }

    /// Add explicit places.
    pub fn places(mut self, places: impl IntoIterator<Item = PlaceRef>) -> Self {
        for p in places {
            self.insert_place(p);
        }
        self
    }

    /// Add a transition (auto-collects places from arcs).
    pub fn transition(mut self, transition: Transition) -> Self {
        // Auto-collect places — order-preserving dedup so the resulting
        // PetriNet's place iteration order matches Java/TS.
        for spec in transition.input_specs() {
            self.insert_place(spec.place().clone());
        }
        for p in transition.output_places() {
            self.insert_place(p.clone());
        }
        for inh in transition.inhibitors() {
            self.insert_place(inh.place.clone());
        }
        for r in transition.reads() {
            self.insert_place(r.place.clone());
        }
        for r in transition.resets() {
            self.insert_place(r.place.clone());
        }
        self.transitions.push(transition);
        self
    }

    /// Add multiple transitions.
    pub fn transitions(mut self, transitions: impl IntoIterator<Item = Transition>) -> Self {
        for t in transitions {
            self = self.transition(t);
        }
        self
    }

    /// Composes a subnet [`Instance`] into this builder per **MOD-020** /
    /// **MOD-023** (composition produces a flat net).
    ///
    /// For each `(port_name -> caller_place)` mapping:
    /// - The instance's renamed port place is substituted with the caller's
    ///   place at every arc in the instance's renamed body.
    /// - Internal (non-port) places of the instance flow through with their
    ///   prefixed names (per **MOD-012** isolation).
    ///
    /// Composition is **eager** — the rewrite happens here, not at
    /// [`PetriNetBuilder::build`] (per [MOD-020] AC #5).
    ///
    /// This overload accepts only port mappings. Channel composition uses the
    /// [`PetriNetBuilder::compose_with`] callback overload.
    ///
    /// # Type compatibility (MOD-022)
    /// Rust does not reify generics on [`PlaceRef`] (the type-erased identity
    /// used by arcs), so this overload performs **no runtime** token-type
    /// check on the caller place. Compile-time safety is provided by the
    /// typed [`compose::ComposeBindingsBuilder::bind_port`] signature on the
    /// callback overload — prefer that overload when type safety matters.
    ///
    /// # Panics
    /// - Panics if any `port_name` is not present on the instance's
    ///   interface; the message names the bad port and lists known ports.
    pub fn compose<P: 'static>(
        self,
        instance: &Instance<P>,
        port_mappings: HashMap<Arc<str>, PlaceRef>,
    ) -> Self {
        compose_internal(self, instance, port_mappings, HashMap::new())
    }

    /// Typed overload of [`PetriNetBuilder::compose`] that accepts a closure
    /// receiving a fresh [`compose::ComposeBindingsBuilder`] per **MOD-020**
    /// (port composition) and **MOD-021** (channel composition).
    ///
    /// The closure registers port and channel bindings; the host builder
    /// drains the recorded mappings and applies them.
    ///
    /// # Channel bindings (MOD-021)
    /// For each recorded `(channel_name -> caller_transition)`, the
    /// instance-side renamed channel transition (resolved via
    /// [`crate::instance::Instance::channel`]) is merged with
    /// `caller_transition` into a single transition in the resulting flat
    /// net via [`crate::rewriter::merge_transitions`]. The merge is
    /// caller-wins for identity (name, priority); see
    /// [`crate::rewriter::merge_transitions`] for the full contract.
    ///
    /// # Panics
    /// - Panics on the same conditions as [`PetriNetBuilder::compose`].
    /// - Panics if any channel name is not declared on the instance's
    ///   interface — the message names the bad channel and lists known
    ///   channel names.
    /// - Panics on conflicting non-`Immediate` timings between the two sides
    ///   of a channel merge (per **MOD-021**).
    pub fn compose_with<P: 'static>(
        self,
        instance: &Instance<P>,
        bind: impl FnOnce(&mut ComposeBindingsBuilder<'_>),
    ) -> Self {
        let mut bindings = ComposeBindingsBuilder::new();
        bind(&mut bindings);
        // Consume the bindings builder, moving the recorded maps into
        // compose_internal directly (no intermediate clone).
        let (port_bindings, channel_bindings) = bindings.into_parts();
        compose_internal(self, instance, port_bindings, channel_bindings)
    }

    /// Identity-default auto-compose per **MOD-024**.
    ///
    /// Each declared interface port auto-binds to its own un-prefixed
    /// host-wiring [`PlaceRef`] — the [`crate::place::Place<T>`] the
    /// [`crate::subnet_def::SubnetDef`] builder declared via
    /// `.input_port(name, place)` / `.output_port(name, place)` /
    /// `.inout_port(name, place)`. If the host builder already declares
    /// an equal-named place, the two are deduped by [`PlaceRef`]'s
    /// name-based [`PartialEq`]/[`Hash`] (see
    /// `spec/11-modular-composition.md` MOD-024 note on name-only matching).
    ///
    /// If the subnet declares no interface ports at all, body places are
    /// matched against the host builder's place set **by name**; matches
    /// are auto-bound, the rest stay private under their prefixed names
    /// per [MOD-010] and [MOD-012].
    ///
    /// Channels are NOT auto-bound — transition identity is too delicate
    /// for inference. If the subnet declares any channel, this method
    /// panics directing the caller to [`PetriNetBuilder::compose_with`].
    ///
    /// # Panics
    /// - Panics when the subnet declares any channel.
    pub fn compose_auto<P: 'static>(self, instance: &Instance<P>) -> Self {
        // Channel guard: auto-compose refuses subnets with channels.
        if instance.channel_handles_keys().next().is_some() {
            let mut channel_names: Vec<&str> =
                instance.channel_handles_keys().map(|n| n.as_ref()).collect();
            channel_names.sort_unstable();
            panic!(
                "compose_auto: subnet '{}' (instance prefix '{}') declares channels [{}]; \
                 auto-compose does not bind channels. \
                 Use compose_with(instance, |b| b.bind_channel(...)) with explicit channel bindings.",
                instance.def_name(),
                instance.prefix(),
                channel_names.join(", ")
            );
        }

        let port_handles = instance.port_handles();
        let prefix_slash = format!("{}/", instance.prefix());

        if !port_handles.is_empty() {
            // Explicit interface path: each port auto-binds to the
            // un-prefixed PlaceRef carried by its declaration. The renamed
            // PlaceRef's name is "{prefix}/{original_place_name}"; strip the
            // prefix to recover the original. When the host pre-declared an
            // equal-named place we prefer its `Arc<str>` to keep identity
            // stable across the merge (matches the explicit-compose path's
            // identity semantics and saves one Arc allocation per port).
            let mut port_mappings: HashMap<Arc<str>, PlaceRef> =
                HashMap::with_capacity(port_handles.len());
            for (port_name, renamed_place) in port_handles {
                let original_name = renamed_place
                    .name_arc()
                    .strip_prefix(prefix_slash.as_str())
                    .map(Arc::<str>::from)
                    .unwrap_or_else(|| Arc::clone(renamed_place.name_arc()));
                let probe = PlaceRef::new(original_name);
                let mapped = self.place_index.get(&probe).cloned().unwrap_or(probe);
                port_mappings.insert(Arc::clone(port_name), mapped);
            }
            return compose_internal(self, instance, port_mappings, HashMap::new());
        }

        // No declared interface — infer the merge set from body places
        // that also exist on this builder. Build the (renamed-name ->
        // host PlaceRef) merge_map directly and short-circuit the
        // port-name validation that compose_internal would otherwise perform.
        let renamed_places = instance.renamed_body().places();
        let mut merge_map: HashMap<Arc<str>, PlaceRef> =
            HashMap::with_capacity(renamed_places.len());
        for renamed in renamed_places {
            // Defensive: rename pass should always prefix body places, but
            // SubnetDef::from_net retrofits may carry un-prefixed places.
            let Some(original) = renamed.name_arc().strip_prefix(prefix_slash.as_str()) else {
                continue;
            };
            let probe = PlaceRef::new(Arc::<str>::from(original));
            if let Some(host) = self.place_index.get(&probe) {
                merge_map.insert(Arc::clone(renamed.name_arc()), host.clone());
            }
        }
        apply_composition(self, instance, merge_map, HashMap::new())
    }

    /// Composes a subnet [`SubnetDef`] **directly** into this builder per
    /// **MOD-025** — **without instantiation**, and without the prefix-
    /// renaming of [`crate::subnet_def::SubnetDef::instantiate`].
    ///
    /// Every body place and transition is added under its **original**
    /// (un-prefixed) name. Places merge into this builder by name: a body
    /// place whose name equals an enclosing-net place *is* that place in the
    /// composed flat net (the builder's place index dedups by name via
    /// [`PlaceRef`]'s name-based [`PartialEq`]/[`Hash`]). This is the mode for
    /// wiring a subnet in as a single shared copy.
    ///
    /// Direct composition is **order-independent**: composing the same set of
    /// subnets in any order yields the same flat net, because merging is by
    /// place name and not by a probe of the builder's place set at call time
    /// — contrast the no-interface body-inference branch of
    /// [`PetriNetBuilder::compose_auto`] (MOD-024), which is order-sensitive.
    ///
    /// For multiple *independent* copies — each with isolated per-instance
    /// state per [MOD-012] — use
    /// [`crate::subnet_def::SubnetDef::instantiate`] followed by
    /// [`PetriNetBuilder::compose`] instead.
    ///
    /// A token-type conflict on a same-named place cannot be detected: Rust
    /// [`PlaceRef`] identity is name-only (the documented carve-out, same as
    /// MOD-024).
    ///
    /// # Panics
    /// - Panics when the subnet's interface declares any channel — direct
    ///   composition does not bind channels; use `instantiate` +
    ///   [`PetriNetBuilder::compose_with`].
    /// - Panics when a body transition's name collides with a transition
    ///   already in this builder — use `instantiate(prefix)` for independent
    ///   copies.
    pub fn compose_direct<P: 'static>(self, def: &SubnetDef<P>) -> Self {
        // MOD-025: direct composition does not bind channels.
        let mut channel_names: Vec<&str> =
            def.iface().channels().map(|c| c.name.as_ref()).collect();
        if !channel_names.is_empty() {
            channel_names.sort_unstable();
            panic!(
                "compose_direct: subnet '{}' declares channels [{}]; direct \
                 composition does not bind channels. Use def.instantiate(prefix) \
                 + compose_with(instance, |b| b.bind_channel(...)).",
                def.name(),
                channel_names.join(", ")
            );
        }

        let body = def.body();

        // MOD-025: a body transition whose name already exists here is almost
        // always a mistake — instantiate(prefix) is the multi-copy path.
        {
            let host_names: HashSet<&str> =
                self.transitions.iter().map(|t| t.name()).collect();
            for t in body.transitions() {
                if host_names.contains(t.name()) {
                    panic!(
                        "compose_direct: transition '{}' from subnet '{}' collides with \
                         a transition already in net '{}'. Direct composition merges by \
                         name; for independent copies use def.instantiate(prefix) + \
                         compose(instance).",
                        t.name(),
                        def.name(),
                        self.name
                    );
                }
            }
        }

        // Rust PlaceRef identity is name-only, so the builder's place index
        // dedups body places against host places by name automatically — no
        // arc rewrite is needed. Add body places first (captures arc-less
        // standalone places), then transitions.
        //
        // MOD-026: record which subnet each node came from so cluster-aware
        // DOT export can reconstruct subgraphs without prefix names. The
        // subnet name is sanitised of '/' so it never triggers spurious
        // nested-cluster splitting in the exporter.
        let subnet_name: Arc<str> = Arc::from(def.name().replace('/', "_"));
        let mut builder = self;
        for p in body.places() {
            let key = Arc::clone(p.name_arc());
            builder = builder.place(p.clone());
            builder
                .subnet_contributions
                .entry(key)
                .or_default()
                .insert(Arc::clone(&subnet_name));
        }
        for t in body.transitions() {
            let key = Arc::clone(t.name_arc());
            builder = builder.transition(t.clone());
            builder
                .subnet_contributions
                .entry(key)
                .or_default()
                .insert(Arc::clone(&subnet_name));
        }
        builder
    }

    /// Registers one or more [`FusionSet`] declarations on this builder, per
    /// **MOD-060** (fusion set declaration) and **MOD-061** (fusion
    /// resolution at build).
    ///
    /// Fusion is **orthogonal to subnet composition**: fuse sets are
    /// accumulated here and applied during [`PetriNetBuilder::build`]
    /// **after** all `compose(...)` calls have flattened subnet instances
    /// into the builder's transition set. Registration order is irrelevant
    /// to semantics — `fuse(set)` BEFORE `compose(...)` and `fuse(set)`
    /// AFTER `compose(...)` both apply at the same point in the build
    /// pipeline.
    ///
    /// # Validation
    /// Cross-set overlap (a place name appearing in two fusion sets) is
    /// detected at [`PetriNetBuilder::build`] and reported as a panic
    /// naming the offending place and both sets.
    pub fn fuse(mut self, sets: impl IntoIterator<Item = FusionSet>) -> Self {
        for s in sets {
            self.fusion_sets.push(s);
        }
        self
    }

    /// Sugar overload of [`PetriNetBuilder::fuse`] that constructs a single
    /// [`FusionSet`] inline via a closure on a fresh [`FuseBuilder`], named
    /// after this enclosing net.
    ///
    /// Equivalent to:
    /// ```ignore
    /// let mut b = FusionSet::builder("<netName>-fusion");
    /// b = b.member(p1).member(p2);
    /// builder.fuse([b.build()]);
    /// ```
    pub fn fuse_with(mut self, sets_builder: impl FnOnce(&mut FuseBuilder)) -> Self {
        let mut fb = FuseBuilder {
            inner: Some(FusionSet::builder(format!("{}-fusion", self.name))),
        };
        sets_builder(&mut fb);
        let inner = fb
            .inner
            .expect("FuseBuilder.inner must remain Some after the closure runs");
        self.fusion_sets.push(inner.build());
        self
    }

    /// Build the [`PetriNet`].
    ///
    /// If any fusion sets were registered via [`PetriNetBuilder::fuse`] or
    /// [`PetriNetBuilder::fuse_with`], applies fusion resolution per
    /// **MOD-061** AFTER all transition/composition accumulation:
    ///
    /// 1. Detect overlapping fusion sets — a single place name declared in
    ///    two sets is rejected via panic.
    /// 2. Build the `non-canonical-name → canonical [`PlaceRef`]`
    ///    substitution map across all sets.
    /// 3. Walk every transition through [`crate::rewriter::apply_fusion`]
    ///    to rewrite arc place references.
    /// 4. Re-derive the place set from the rewritten transitions plus any
    ///    caller-declared standalone places, dropping non-canonical members.
    ///
    /// If no fusion sets were registered, the build is the trivial
    /// `PetriNet { name, places, transitions }` — the fusion machinery has
    /// no per-build cost when unused.
    ///
    /// # Panics
    /// Panics when two fusion sets share a place name.
    pub fn build(self) -> PetriNet {
        let membership = resolve_subnet_membership(&self.subnet_contributions);
        if self.fusion_sets.is_empty() {
            return PetriNet {
                name: self.name,
                places: self.places,
                transitions: self.transitions,
                subnet_membership: membership,
            };
        }
        build_with_fusion(self, membership)
    }
}

/// Resolves the per-`compose_direct` contributions into the final
/// `node-name -> subnet-name` membership map per **MOD-026**. A node
/// contributed by exactly one subnet maps to that subnet; a place
/// contributed by two or more subnets is a shared rendezvous place and is
/// omitted (it renders top-level, outside any cluster). Returns an empty
/// map — the common case — when no subnet was composed directly.
fn resolve_subnet_membership(
    contributions: &HashMap<Arc<str>, HashSet<Arc<str>>>,
) -> HashMap<Arc<str>, Arc<str>> {
    let mut resolved: HashMap<Arc<str>, Arc<str>> = HashMap::new();
    for (node, owners) in contributions {
        if owners.len() == 1 {
            let owner = owners.iter().next().expect("len == 1");
            resolved.insert(Arc::clone(node), Arc::clone(owner));
        }
    }
    resolved
}

/// Sugar collector handed to [`PetriNetBuilder::fuse_with`].
///
/// The closure receives a `&mut FuseBuilder` and registers members via the
/// typed [`FuseBuilder::member`] method. The wrapping
/// [`PetriNetBuilder::fuse_with`] machinery owns the inner
/// [`FusionSetBuilder`] across the closure boundary so the typed `<T>`
/// pinning carries through unchanged.
pub struct FuseBuilder {
    inner: Option<FusionSetBuilder>,
}

impl FuseBuilder {
    /// Appends a member to the inner [`FusionSet`]. The first member becomes
    /// the canonical place per the convention documented on
    /// [`crate::fusion::FusionSet`].
    pub fn member<T: 'static>(&mut self, place: &crate::place::Place<T>) -> &mut Self {
        let inner = self
            .inner
            .take()
            .expect("FuseBuilder.member: inner builder was already consumed");
        self.inner = Some(inner.member(place));
        self
    }
}

/// Fusion-resolution pass per **MOD-061**. Split out from
/// [`PetriNetBuilder::build`] so the no-fusion fast path stays trivial.
///
/// `membership` is the resolved MOD-026 subnet-membership map; it is
/// filtered here so entries naming a non-canonical fused place — which no
/// longer exists in the net — are dropped (the surviving canonical place
/// keeps its own entry).
fn build_with_fusion(
    builder: PetriNetBuilder,
    membership: HashMap<Arc<str>, Arc<str>>,
) -> PetriNet {
    let PetriNetBuilder {
        name,
        places,
        place_index: _,
        transitions,
        fusion_sets,
        subnet_contributions: _,
    } = builder;

    // Step 1: detect overlap. The same place name MUST NOT appear in more
    // than one fusion set (Rust place identity is name-based, matching the
    // PlaceRef Hash/Eq contract).
    //
    // Keying ownership by `Arc<str>` (the place's name) and pointing back at
    // the owning fusion set's index lets us raise a contextual error message
    // naming both sets when an overlap is detected.
    let mut ownership: HashMap<Arc<str>, usize> = HashMap::new();
    for (idx, set) in fusion_sets.iter().enumerate() {
        for member in set.members() {
            if let Some(&prior_idx) = ownership.get(member.name_arc()) {
                if prior_idx != idx {
                    let prior = &fusion_sets[prior_idx];
                    panic!(
                        "Fusion overlap: place '{}' appears in two fusion sets ('{}' and \
                         '{}'). A place may appear in at most one fusion set (MOD-060).",
                        member.name(),
                        prior.name(),
                        set.name()
                    );
                }
            } else {
                ownership.insert(Arc::clone(member.name_arc()), idx);
            }
        }
    }

    // Step 2: build the non-canonical-name → canonical PlaceRef substitution
    // map. Single-member sets contribute nothing (no non-canonical members),
    // so the map is naturally empty for the degenerate case.
    let mut fusion_map: HashMap<Arc<str>, PlaceRef> = HashMap::new();
    let mut non_canonical_names: HashSet<Arc<str>> = HashSet::new();
    for set in &fusion_sets {
        let canonical = set.canonical().clone();
        for nc in set.non_canonical() {
            fusion_map.insert(Arc::clone(nc.name_arc()), canonical.clone());
            non_canonical_names.insert(Arc::clone(nc.name_arc()));
        }
    }

    // Step 3: rewrite every transition's arcs through the fusion map.
    // apply_fusion always returns a fresh Vec; if fusion_map is empty (single-
    // member-only sets) the rewrite is structurally a no-op but still rebuilds
    // Transition records — no observable difference.
    let rewritten_transitions = rewriter::apply_fusion(transitions, &fusion_map);

    // Step 4: re-derive the place set. Strategy: start from the current
    // place list (preserving builder insertion order), drop every
    // non-canonical member (they are gone from the net), then union in
    // the places auto-discovered from the rewritten transitions. This
    // preserves caller-declared standalone places that are unrelated to
    // fusion, drops any standalone declarations of non-canonical members,
    // and ensures canonical places end up present even if a caller never
    // declared them standalone.
    //
    // Order-preserving dedup via a parallel `seen` HashSet — the resulting
    // PetriNet's `places()` iteration order must remain deterministic for
    // the cross-language byte-parity contract.
    let mut rebuilt_places: Vec<PlaceRef> = Vec::with_capacity(places.len() + 16);
    let mut seen: HashSet<PlaceRef> = HashSet::with_capacity(places.len() + 16);
    let push = |p: PlaceRef, seen: &mut HashSet<PlaceRef>, dst: &mut Vec<PlaceRef>| {
        if seen.insert(p.clone()) {
            dst.push(p);
        }
    };
    for p in &places {
        if !non_canonical_names.contains(p.name_arc()) {
            push(p.clone(), &mut seen, &mut rebuilt_places);
        }
    }
    for t in &rewritten_transitions {
        for spec in t.input_specs() {
            push(spec.place().clone(), &mut seen, &mut rebuilt_places);
        }
        for p in t.output_places() {
            push(p.clone(), &mut seen, &mut rebuilt_places);
        }
        for inh in t.inhibitors() {
            push(inh.place.clone(), &mut seen, &mut rebuilt_places);
        }
        for r in t.reads() {
            push(r.place.clone(), &mut seen, &mut rebuilt_places);
        }
        for r in t.resets() {
            push(r.place.clone(), &mut seen, &mut rebuilt_places);
        }
    }

    // MOD-026: drop membership entries for places removed by fusion. A
    // non-canonical fused member no longer exists in the net, so its
    // `node-name -> subnet` entry would dangle. The surviving canonical
    // place keeps its entry. Transitions are never fused away, so their
    // entries always survive.
    let filtered_membership: HashMap<Arc<str>, Arc<str>> =
        if membership.is_empty() || non_canonical_names.is_empty() {
            membership
        } else {
            membership
                .into_iter()
                .filter(|(node, _)| !non_canonical_names.contains(node))
                .collect()
        };

    PetriNet {
        name,
        places: rebuilt_places,
        transitions: rewritten_transitions,
        subnet_membership: filtered_membership,
    }
}

/// Shared compose implementation: validates port and channel bindings,
/// builds the place-substitution map, walks every renamed-body transition
/// through [`crate::rewriter::substitute_places`], folds channel-bound
/// transitions through [`crate::rewriter::merge_transitions`], and adds the
/// resulting transitions to the supplied builder.
///
/// # Algorithm
/// 1. For each `(port_name, caller_place)`:
///    - Look up the renamed instance-side place via `instance.port_handles`
///      (keyed by original port name) — the [`Instance::port`] machinery
///      already resolves this against the interface's declared `TypeId`.
///    - On unknown port name, panic with a message listing all known ports.
///    - Insert `(renamed_iface_place_name -> caller_place)` into the merge
///      map. The rewriter resolves arc places by name (matching the
///      [`crate::place::PlaceRef`] identity model), so the key is the
///      renamed name (post-prefix), not the original.
/// 2. Walk every transition of `instance.renamed_body()`. For each, call
///    [`crate::rewriter::substitute_places`] and stage the rewritten
///    transition in a name-keyed working map (insertion-order preserved via
///    a parallel `Vec<Arc<str>>`). The substitute primitive keeps the
///    prefixed transition name unchanged (per **MOD-010** — prefixed names
///    are already unique within the host) and rewrites only the arc place
///    references.
/// 3. For each `(channel_name, caller_transition)`:
///    - Resolve the renamed instance-side transition name via
///      `instance.channel(channel_name)` (panics on unknown channel — the
///      message names the bad channel and lists known channels).
///    - Apply the same place substitution to `caller_transition` so the
///      caller-side arcs are also rewritten through the port map.
///    - Merge via [`crate::rewriter::merge_transitions`] under
///      `caller.name()` (caller-wins identity per **MOD-021**).
///    - Replace the staged renamed instance-side entry with the merged
///      transition under the merged name (drop the renamed name).
/// 4. Drain the staged map into the host builder in insertion order so the
///    transitions land deterministically.
fn compose_internal<P: 'static>(
    builder: PetriNetBuilder,
    instance: &Instance<P>,
    port_mappings: HashMap<Arc<str>, PlaceRef>,
    channel_bindings: HashMap<Arc<str>, Transition>,
) -> PetriNetBuilder {
    let port_handles = instance.port_handles();

    // Build merge_map: keyed by RENAMED instance-side place name (Arc<str>)
    // -> caller PlaceRef. Pre-size for the no-realloc hot path. The
    // rewriter resolves arc places by name (matching the PlaceRef identity
    // model in compiled_net.rs), so the key is the renamed (post-prefix)
    // name, not the original port name.
    let mut merge_map: HashMap<Arc<str>, PlaceRef> =
        HashMap::with_capacity(port_mappings.len());

    for (port_name, caller_place) in &port_mappings {
        // Validate the port name is known on the instance and resolve to
        // the renamed (post-prefix) instance-side place via the port_handles
        // map (populated by SubnetDef::instantiate). On unknown name, panic
        // with a sorted list of known ports.
        let renamed_iface = port_handles.get(port_name).unwrap_or_else(|| {
            let mut known: Vec<&str> =
                port_handles.keys().map(|n| n.as_ref()).collect();
            known.sort_unstable();
            panic!(
                "compose: no port named '{}' on subnet '{}' (instance prefix '{}'). \
                 Known ports: [{}]",
                port_name,
                instance.def_name(),
                instance.prefix(),
                known.join(", ")
            );
        });
        merge_map.insert(Arc::clone(renamed_iface.name_arc()), caller_place.clone());
    }

    apply_composition(builder, instance, merge_map, channel_bindings)
}

/// Shared post-merge-map composition pipeline used by both the explicit-
/// binding paths ([`PetriNetBuilder::compose`] / [`PetriNetBuilder::compose_with`])
/// and the auto-compose path ([`PetriNetBuilder::compose_auto`] per **MOD-024**).
/// The two paths differ only in how the (renamed Place name -> host PlaceRef)
/// `merge_map` is built.
fn apply_composition<P: 'static>(
    mut builder: PetriNetBuilder,
    instance: &Instance<P>,
    merge_map: HashMap<Arc<str>, PlaceRef>,
    channel_bindings: HashMap<Arc<str>, Transition>,
) -> PetriNetBuilder {
    // ============================================================
    //  Working transition map (mirror Java's LinkedHashMap)
    // ============================================================
    //
    // Stage every rewritten instance-side transition into a name-keyed map
    // so channel bindings can replace specific entries in O(1). A parallel
    // `Vec<Arc<str>>` preserves insertion order so the resulting builder
    // sees transitions in the same order they appear in the renamed body
    // (deterministic, matching Java's LinkedHashMap iteration semantics).
    //
    // Pre-sized for the no-realloc hot path: capacity matches the renamed
    // body's transition count.
    let renamed_body = instance.renamed_body();
    let cap = renamed_body.transitions().len();
    let mut staged: HashMap<Arc<str>, Transition> = HashMap::with_capacity(cap);
    let mut order: Vec<Arc<str>> = Vec::with_capacity(cap);

    for t in renamed_body.transitions() {
        let rewritten = rewriter::substitute_places(t, &merge_map);
        let name = Arc::clone(rewritten.name_arc());
        staged.insert(Arc::clone(&name), rewritten);
        order.push(name);
    }

    // ============================================================
    //  Channel composition (MOD-021)
    // ============================================================
    //
    // For each binding, resolve the renamed instance-side transition by name
    // via `instance.channel(...)`, apply the same port-place substitution to
    // the caller-side transition, then merge under `caller.name()`. Replace
    // the staged renamed entry in-place — we drop the renamed name from the
    // working map and the order vector, and stage the merged transition
    // under the caller's name. This matches the Java/TS semantics where the
    // merged transition replaces both sides in the resulting flat net.
    for (channel_name, caller_t) in &channel_bindings {
        // Validate the channel name is known on the instance. On unknown
        // name, panic with a sorted list of known channels.
        let renamed_name: Arc<str> = match instance.channel_handles_get(channel_name) {
            Some(n) => Arc::clone(n),
            None => {
                let mut known: Vec<&str> = instance
                    .channel_handles_keys()
                    .map(|n| n.as_ref())
                    .collect();
                known.sort_unstable();
                panic!(
                    "compose: no channel named '{}' on subnet '{}' (instance prefix '{}'). \
                     Known channels: [{}]",
                    channel_name,
                    instance.def_name(),
                    instance.prefix(),
                    known.join(", ")
                );
            }
        };

        // The instance-side transition must be in the working map (it was
        // staged in step 2). Remove it — we replace it with the merged
        // version under the caller's name.
        let instance_t = staged.remove(&renamed_name).unwrap_or_else(|| {
            panic!(
                "compose: channel '{}' resolved to instance-side transition '{}' which was not \
                 staged from the renamed body — this is a libpetri internal invariant violation",
                channel_name, renamed_name
            )
        });

        // Apply the same port-place substitution to the caller-side
        // transition's arcs so caller-side arcs that reference port-mapped
        // places also resolve correctly. The caller's transition retains
        // its name (per substitute_places semantics).
        let rewritten_caller = rewriter::substitute_places(caller_t, &merge_map);
        let merged_name: Arc<str> = Arc::clone(rewritten_caller.name_arc());

        // Merge: caller-side wins identity (name, priority); arcs union;
        // outputs wrap under Out::And; actions compose sequentially.
        let merged = rewriter::merge_transitions(&rewritten_caller, &instance_t, Arc::clone(&merged_name));

        // Replace the renamed name in the order vector with the merged
        // name (preserving insertion order: the channel-merged transition
        // lands at the position where the instance-side transition was).
        // This matches Java's LinkedHashMap semantics: the merged entry
        // replaces the renamed entry under a different key, but at the
        // same iteration slot.
        if let Some(pos) = order.iter().position(|n| n.as_ref() == renamed_name.as_ref()) {
            order[pos] = Arc::clone(&merged_name);
        } else {
            // Defensive: every staged transition has its name in the order
            // vector by construction; fall through to append rather than
            // panic so a logic bug here doesn't lose the merged transition.
            order.push(Arc::clone(&merged_name));
        }
        staged.insert(merged_name, merged);
    }

    // Drain the staged map into the host builder in insertion order. We
    // pull from `staged` by name through the `order` vector to preserve
    // determinism. Each call to `builder.transition(...)` auto-collects the
    // transition's places (matching the existing pre-#21 behaviour).
    for name in &order {
        if let Some(t) = staged.remove(name) {
            builder = builder.transition(t);
        }
    }

    builder
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::one;
    use crate::output::out_place;
    use crate::place::Place;

    #[test]
    fn petri_net_builder_auto_collects_places() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();

        let net = PetriNet::builder("test").transition(t).build();

        assert_eq!(net.places().len(), 2);
        assert!(net.places().contains(&PlaceRef::new("p1")));
        assert!(net.places().contains(&PlaceRef::new("p2")));
        assert_eq!(net.transitions().len(), 1);
    }

    #[test]
    fn petri_net_explicit_places() {
        let net = PetriNet::builder("test")
            .place(PlaceRef::new("orphan"))
            .build();

        assert_eq!(net.places().len(), 1);
        assert!(net.places().contains(&PlaceRef::new("orphan")));
    }

    #[test]
    fn petri_net_bind_actions() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();

        let net = PetriNet::builder("test").transition(t).build();
        assert!(net.transitions()[0].action().is_sync());

        // Bind a new action
        let mut bindings = std::collections::HashMap::new();
        bindings.insert("t1".to_string(), crate::action::passthrough());
        let net2 = net.bind_actions(&bindings);
        assert_eq!(net2.transitions().len(), 1);
        assert_eq!(net2.transitions()[0].name(), "t1");
    }

    // ============================================================
    //  MOD-026: subnet-membership metadata for direct composition
    // ============================================================

    /// A producer subnet whose output place is named `pipe` (wires by name).
    fn pipe_producer() -> SubnetDef<()> {
        let seed = Place::<String>::new("seed");
        let pipe = Place::<String>::new("pipe");
        SubnetDef::<()>::builder("PipeProducer")
            .place(&seed)
            .place(&pipe)
            .transition(
                Transition::builder("emit")
                    .input(one(&seed))
                    .output(out_place(&pipe))
                    .build(),
            )
            .build()
    }

    /// A consumer subnet whose input place is named `pipe` (wires by name).
    fn pipe_consumer() -> SubnetDef<()> {
        let pipe = Place::<String>::new("pipe");
        let sink = Place::<String>::new("sink");
        SubnetDef::<()>::builder("PipeConsumer")
            .place(&pipe)
            .place(&sink)
            .transition(
                Transition::builder("eat")
                    .input(one(&pipe))
                    .output(out_place(&sink))
                    .build(),
            )
            .build()
    }

    #[test]
    fn direct_compose_records_membership_per_subnet() {
        let net = PetriNet::builder("Host")
            .compose_direct(&pipe_producer())
            .compose_direct(&pipe_consumer())
            .build();

        let m = net.subnet_membership();
        assert_eq!(m.get("seed").map(|s| s.as_ref()), Some("PipeProducer"));
        assert_eq!(m.get("emit").map(|s| s.as_ref()), Some("PipeProducer"));
        assert_eq!(m.get("sink").map(|s| s.as_ref()), Some("PipeConsumer"));
        assert_eq!(m.get("eat").map(|s| s.as_ref()), Some("PipeConsumer"));
    }

    #[test]
    fn direct_compose_shared_place_has_no_membership_entry() {
        // 'pipe' is contributed by both subnets — a shared rendezvous place
        // with no single owner, so it carries no membership entry.
        let net = PetriNet::builder("Host")
            .compose_direct(&pipe_producer())
            .compose_direct(&pipe_consumer())
            .build();

        assert!(
            !net.subnet_membership().contains_key("pipe"),
            "a place contributed by 2+ subnets must have no membership entry"
        );
    }

    #[test]
    fn direct_compose_membership_is_order_independent() {
        let ab = PetriNet::builder("Host")
            .compose_direct(&pipe_producer())
            .compose_direct(&pipe_consumer())
            .build();
        let ba = PetriNet::builder("Host")
            .compose_direct(&pipe_consumer())
            .compose_direct(&pipe_producer())
            .build();

        assert_eq!(
            ab.subnet_membership(),
            ba.subnet_membership(),
            "membership must not depend on compose order"
        );
    }

    #[test]
    fn flat_net_has_empty_membership() {
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let net = PetriNet::builder("Flat")
            .transition(
                Transition::builder("move")
                    .input(one(&a))
                    .output(out_place(&b))
                    .build(),
            )
            .build();

        assert!(
            net.subnet_membership().is_empty(),
            "a hand-written flat net carries no subnet membership"
        );
    }

    #[test]
    fn instance_compose_has_empty_membership() {
        // compose_auto is the prefix-rename path — it records no membership;
        // the exporter clusters those nodes by name prefix.
        let p_in = Place::<String>::new("in");
        let p_out = Place::<String>::new("out");
        let producer = SubnetDef::<()>::builder("Producer")
            .input_port("in", &p_in)
            .output_port("out", &p_out)
            .transition(
                Transition::builder("produce")
                    .input(one(&p_in))
                    .output(out_place(&p_out))
                    .build(),
            )
            .build();
        let instance = producer.instantiate_unit("p1");
        let net = PetriNet::builder("Host").compose_auto(&instance).build();

        assert!(
            net.subnet_membership().is_empty(),
            "instance composition records no membership metadata"
        );
    }

    #[test]
    fn direct_compose_then_fuse_drops_non_canonical_entry() {
        // Fusion removes the non-canonical place 'b'; its membership entry
        // must be dropped so the map names only places that still exist.
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let subnet = SubnetDef::<()>::builder("AB")
            .transition(
                Transition::builder("move")
                    .input(one(&a))
                    .output(out_place(&b))
                    .build(),
            )
            .build();

        let net = PetriNet::builder("Host")
            .compose_direct(&subnet)
            .fuse([FusionSet::of("ab", &a, &[&b])])
            .build();

        assert_eq!(
            net.subnet_membership().get("a").map(|s| s.as_ref()),
            Some("AB"),
            "the canonical fused place keeps its membership entry"
        );
        assert!(
            !net.subnet_membership().contains_key("b"),
            "the non-canonical fused place must lose its membership entry"
        );
        assert_eq!(
            net.subnet_membership().get("move").map(|s| s.as_ref()),
            Some("AB"),
            "transitions are unaffected by fusion"
        );
    }

    #[test]
    fn bind_actions_preserves_membership() {
        let net = PetriNet::builder("Host")
            .compose_direct(&pipe_producer())
            .compose_direct(&pipe_consumer())
            .build();

        let mut bindings = std::collections::HashMap::new();
        bindings.insert("emit".to_string(), crate::action::passthrough());
        let bound = net.bind_actions(&bindings);

        assert_eq!(
            net.subnet_membership(),
            bound.subnet_membership(),
            "bind_actions rebuilds transitions by name — membership must survive"
        );
    }

    #[test]
    fn direct_compose_subnet_name_with_slash_is_sanitised() {
        // A subnet name containing '/' must be sanitised so it never triggers
        // spurious nested-cluster splitting in the exporter.
        let x = Place::<String>::new("x");
        let y = Place::<String>::new("y");
        let subnet = SubnetDef::<()>::builder("group/sub")
            .transition(
                Transition::builder("step")
                    .input(one(&x))
                    .output(out_place(&y))
                    .build(),
            )
            .build();

        let net = PetriNet::builder("Host").compose_direct(&subnet).build();

        assert_eq!(
            net.subnet_membership().get("step").map(|s| s.as_ref()),
            Some("group_sub"),
            "'/' in a subnet name must be replaced with '_'"
        );
    }

    #[test]
    fn petri_net_collects_inhibitor_read_reset_places() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");
        let p_inh = Place::<i32>::new("inh");
        let p_read = Place::<i32>::new("read");
        let p_reset = Place::<i32>::new("reset");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .inhibitor(crate::arc::inhibitor(&p_inh))
            .read(crate::arc::read(&p_read))
            .reset(crate::arc::reset(&p_reset))
            .build();

        let net = PetriNet::builder("test").transition(t).build();
        assert_eq!(net.places().len(), 5);
    }
}
