/**
 * @module open-net/contract
 *
 * What a subnet promises when verified on its own, with its ports played by the environment
 * ([VER-022]).
 *
 * The **assumption**: the tokens the subnet holds before anything arrives, and arrival
 * groups, each delivering between `min` and `max` tokens onto its places at any point of the
 * run. Every bound is finite: a bound is both the runtime cap and the width of the claim.
 *
 * The **guarantee**: at every quiescent marking the count clauses hold, and tokens rest only
 * on clause, rest or environment places, or where a marked designed terminal excuses them;
 * every other place is internal and empty. Every run comes to rest unless
 * {@link OpenNetContractBuilder.requireTermination} is turned off.
 */
import type { Place } from '../../core/place.js';
import type { Transition } from '../../core/transition.js';
import { MarkingState, type MarkingStateBuilder } from '../marking-state.js';
import { countPhrase } from '../count-clause.js';

/**
 * The environment delivers between `min` and `max` tokens in total, each onto one of
 * `places`, each at any point of the run.
 */
export interface ArrivalGroup {
  readonly places: readonly Place<any>[];
  readonly min: number;
  readonly max: number;
}

/**
 * At every quiescent marking the tokens across `places` number between `min` and `max`
 * (`max` may be `Infinity`). A marked designed terminal waives `min`, never `max`: a halt
 * stops progress, it does not license a token too many.
 */
export interface CountClause {
  readonly name: string;
  readonly places: readonly Place<any>[];
  readonly min: number;
  readonly max: number;
}

/**
 * While `marker` holds a token, the clauses' lower bounds are waived and tokens may rest on
 * `excused`: the places where the work the marker interrupted was delivered. The marker
 * itself may always rest, as a conditional-sink marker may ([VER-014]).
 */
export interface DesignedTerminal {
  readonly marker: Place<any>;
  readonly excused: readonly Place<any>[];
}

const CONTRACT_KEY = Symbol('OpenNetContract.internal');

/**
 * A subnet's contract: the environment it assumes and what it guarantees at quiescence
 * ([VER-022]). Build one with {@link OpenNetContract.builder}; check it with `verifyOpenNet`.
 *
 * ```ts
 * const contract = OpenNetContract.builder()
 *   .initialMarking(m => m.tokens(idle, 1).tokens(budget, k))
 *   .arrive(1, inData, inEmpty)          // exactly one arrival on the input edge
 *   .arriveAtMost(1, halt)               // never or once
 *   .expect('e3', 1, e3Data, e3Empty)    // one of data / empty per outgoing edge, once it runs
 *   .expect('idle', 1, idle)
 *   .expect('budget', k, budget)
 *   .expect('history', 1, done, skipped)
 *   .terminal(halt, inData, inEmpty)     // a halted run leaves the arrival where it was delivered
 *   .terminal(skipped)                   // a skipped run writes no output edge at all
 *   .build();
 * ```
 *
 * **A node that can skip needs its edge clauses conditional.** `expect('e3', 1, …)` alone
 * reports a node that rests having skipped the edge. Name the place that marks a skip as a
 * {@link OpenNetContractBuilder.terminal}: while it is marked the lower bounds are waived, and
 * the upper bounds still catch an edge written twice.
 *
 * **A subnet that asks something of its neighbours needs an environment.** Alone, a node that
 * sends a request and waits quiesces with the request outstanding. Give the contract the
 * transitions the neighbours fire; their own places are never counted as stranded.
 *
 * ```ts
 * // A node that runs again on every answer, against an environment that answers twice.
 * const again = Transition.builder('env/again').inputs(one(request), one(rounds))
 *   .outputs(outPlace(reply)).build();
 * const end = Transition.builder('env/end').inputs(one(request)).outputs(outPlace(ended)).build();
 *
 * const agent = OpenNetContract.builder()
 *   .initialMarking(m => m.tokens(rounds, 2))   // the environment's own budget
 *   .arrive(1, inPlace)
 *   .expectBetween('done', 0, 1, done)          // it may end without finishing
 *   .environment(again, end)
 *   .build();
 * ```
 *
 * An environment transition is never executed, so it needs no action.
 */
export class OpenNetContract {
  /** Tokens the subnet holds before anything arrives: its own resources and any shared pool it borrows from. */
  readonly initialMarking: MarkingState;
  readonly arrivals: readonly ArrivalGroup[];
  readonly clauses: readonly CountClause[];
  /** Places that may hold any number of tokens at quiescence. */
  readonly rest: readonly Place<any>[];
  readonly terminals: readonly DesignedTerminal[];
  /** Transitions the environment fires: neighbours that react to what the subnet sends. */
  readonly environment: readonly Transition[];
  /** Whether every run must come to rest. */
  readonly requiresTermination: boolean;

  /** @internal Use {@link OpenNetContract.builder}. */
  constructor(
    key: symbol,
    initialMarking: MarkingState,
    arrivals: readonly ArrivalGroup[],
    clauses: readonly CountClause[],
    rest: readonly Place<any>[],
    terminals: readonly DesignedTerminal[],
    environment: readonly Transition[],
    requiresTermination: boolean,
  ) {
    if (key !== CONTRACT_KEY) throw new Error('Use OpenNetContract.builder() to create instances');
    this.initialMarking = initialMarking;
    this.arrivals = arrivals;
    this.clauses = clauses;
    this.rest = rest;
    this.terminals = terminals;
    this.environment = environment;
    this.requiresTermination = requiresTermination;
  }

  static builder(): OpenNetContractBuilder {
    return new OpenNetContractBuilder();
  }

  /**
   * Every place the initial marking, an arrival group, a clause, the rest set or a terminal
   * marker names, then every place an environment transition touches, in first-mention
   * order: the places a port trace reports. A terminal's excused places are not included;
   * `closeOpenNet` adds them to the closed net itself.
   */
  places(): Place<any>[] {
    const seen = new Map<string, Place<any>>();
    const add = (p: Place<any>): void => {
      if (!seen.has(p.name)) seen.set(p.name, p);
    };
    for (const p of this.initialMarking.placesWithTokens()) add(p);
    for (const g of this.arrivals) g.places.forEach(add);
    for (const c of this.clauses) c.places.forEach(add);
    this.rest.forEach(add);
    for (const t of this.terminals) add(t.marker);
    for (const t of this.environment) transitionPlaces(t).forEach(add);
    return [...seen.values()];
  }

  /** The contract as the report prints it, one line per part. */
  describe(): string[] {
    const names = (ps: readonly Place<any>[]): string => ps.map(p => p.name).join(', ');
    const lines = [`  Initial marking: ${this.initialMarking.toString()}`];
    lines.push(this.arrivals.length === 0
      ? '  Arrivals: none'
      : `  Arrivals: ${this.arrivals.map(g => `${countPhrase(g.min, g.max)} onto {${names(g.places)}}`).join('; ')}`);
    lines.push(this.clauses.length === 0
      ? '  At quiescence: no count clauses'
      : `  At quiescence: ${this.clauses.map(c => `${c.name} = ${countPhrase(c.min, c.max)} across {${names(c.places)}}`).join('; ')}`);
    if (this.rest.length > 0) lines.push(`  Rest: ${names(this.rest)}`);
    for (const t of this.terminals) {
      lines.push(t.excused.length === 0
        ? `  Terminal: when ${t.marker.name}`
        : `  Terminal: when ${t.marker.name}: ${names(t.excused)}`);
    }
    if (this.environment.length > 0) {
      lines.push(`  Environment transitions: ${this.environment.map(t => t.name).join(', ')}`);
    }
    lines.push(`  Termination: ${this.requiresTermination ? 'every run comes to rest' : 'not required'}`);
    return lines;
  }
}

/**
 * @internal `contract` with each of `markers` merged in as a designed terminal excusing
 * `excused`: the form net-declared terminal places take on the open-net route ([EXEC-042],
 * [VER-014]). A marker the contract already names keeps its position and gains the excuses.
 * One rebuild for every marker, not one per marker.
 */
export function withDesignedTerminals(
  contract: OpenNetContract,
  markers: Iterable<Place<any>>,
  excused: readonly Place<any>[],
): OpenNetContract {
  const b = new OpenNetContractBuilder()
    .initialMarking(contract.initialMarking)
    .requireTermination(contract.requiresTermination);
  for (const g of contract.arrivals) b.arriveBetween(g.min, g.max, ...g.places);
  for (const c of contract.clauses) b.expectBetween(c.name, c.min, c.max, ...c.places);
  if (contract.rest.length > 0) b.rest(...contract.rest);
  for (const t of contract.terminals) b.terminal(t.marker, ...t.excused);
  for (const marker of markers) b.terminal(marker, ...excused);
  if (contract.environment.length > 0) b.environment(...contract.environment);
  return b.build();
}

/** Every place an arc of `t` touches: inputs, reads, inhibitors, resets, then outputs. */
export function transitionPlaces(t: Transition): Place<any>[] {
  return [
    ...t.inputSpecs.map(s => s.place),
    ...t.reads.map(a => a.place),
    ...t.inhibitors.map(a => a.place),
    ...t.resets.map(a => a.place),
    ...t.outputPlaces(),
  ];
}

export class OpenNetContractBuilder {
  private _initialMarking: MarkingState = MarkingState.empty();
  private readonly _arrivals: ArrivalGroup[] = [];
  private readonly _clauses: CountClause[] = [];
  private readonly _rest = new Map<string, Place<any>>();
  private readonly _terminals: { marker: Place<any>; excused: Map<string, Place<any>> }[] = [];
  private readonly _environment: Transition[] = [];
  private _requiresTermination = true;

  /** Tokens the subnet holds before anything arrives. */
  initialMarking(marking: MarkingState): this;
  initialMarking(configurator: (builder: MarkingStateBuilder) => void): this;
  initialMarking(arg: MarkingState | ((builder: MarkingStateBuilder) => void)): this {
    if (arg instanceof MarkingState) {
      this._initialMarking = arg;
    } else {
      const builder = MarkingState.builder();
      arg(builder);
      this._initialMarking = builder.build();
    }
    return this;
  }

  /** The environment delivers exactly `count` tokens, each onto one of `places`, at any point of the run. */
  arrive(count: number, ...places: Place<any>[]): this {
    return this.arriveBetween(count, count, ...places);
  }

  /** The environment delivers at most `max` tokens, possibly none. `arriveAtMost(1, halt)` is "never or once". */
  arriveAtMost(max: number, ...places: Place<any>[]): this {
    return this.arriveBetween(0, max, ...places);
  }

  /** The environment delivers between `min` and `max` tokens in total, each onto one of `places`, at any point of the run. */
  arriveBetween(min: number, max: number, ...places: Place<any>[]): this {
    if (!Number.isInteger(min) || !Number.isInteger(max) || min < 0 || max < min || max < 1) {
      throw new Error(
        `OpenNetContract: an arrival group needs whole bounds with 0 <= min <= max and max >= 1, ` +
        `got ${min}..${max}. A bound is both the runtime cap and the width of the claim, so it is finite.`,
      );
    }
    this._arrivals.push({ places: distinct(places, 'an arrival group'), min, max });
    return this;
  }

  /** At every quiescent marking, exactly `count` tokens across `places`. */
  expect(name: string, count: number, ...places: Place<any>[]): this {
    return this.expectBetween(name, count, count, ...places);
  }

  /** At every quiescent marking, between `min` and `max` tokens across `places`; `max` may be `Infinity`. */
  expectBetween(name: string, min: number, max: number, ...places: Place<any>[]): this {
    if (name.length === 0) throw new Error('OpenNetContract: a clause needs a name');
    if (this._clauses.some(c => c.name === name)) {
      throw new Error(`OpenNetContract: duplicate clause name '${name}'`);
    }
    if (!Number.isInteger(min) || min < 0 || !(max === Infinity || Number.isInteger(max)) || max < min) {
      throw new Error(`OpenNetContract: clause '${name}' needs whole bounds with 0 <= min <= max, got ${min}..${max}`);
    }
    this._clauses.push({ name, places: distinct(places, `clause '${name}'`), min, max });
    return this;
  }

  /** Places that may hold any number of tokens at quiescence. */
  rest(...places: Place<any>[]): this {
    for (const p of places) if (!this._rest.has(p.name)) this._rest.set(p.name, p);
    return this;
  }

  /**
   * A designed terminal: while `marker` holds a token, lower bounds are waived and tokens may
   * rest on `excused`. Repeated calls for one marker accumulate.
   */
  terminal(marker: Place<any>, ...excused: Place<any>[]): this {
    let entry = this._terminals.find(t => t.marker.name === marker.name);
    if (entry == null) {
      entry = { marker, excused: new Map() };
      this._terminals.push(entry);
    }
    for (const p of excused) if (!entry.excused.has(p.name)) entry.excused.set(p.name, p);
    return this;
  }

  /**
   * Transitions the environment fires: a neighbour that reacts to what the subnet sends, such
   * as a tool answering a request. An arrival group cannot say that: its tokens do not wait
   * for a request.
   *
   * They join the closed net unchanged and are marked as environment steps in the port trace.
   * A place only they touch belongs to the environment and may hold tokens at quiescence; a
   * place they share with the subnet is a port, judged like any other. Their actions never
   * run, so one that declares outputs may keep `passthrough()`.
   */
  environment(...transitions: Transition[]): this {
    for (const t of transitions) {
      if (this._environment.some(e => e.name === t.name)) {
        throw new Error(`OpenNetContract: duplicate environment transition '${t.name}'`);
      }
      this._environment.push(t);
    }
    return this;
  }

  /** Whether every run must come to rest (default `true`). */
  requireTermination(required: boolean): this {
    this._requiresTermination = required;
    return this;
  }

  build(): OpenNetContract {
    return new OpenNetContract(
      CONTRACT_KEY,
      this._initialMarking,
      [...this._arrivals],
      [...this._clauses],
      [...this._rest.values()],
      this._terminals.map(t => ({ marker: t.marker, excused: [...t.excused.values()] })),
      [...this._environment],
      this._requiresTermination,
    );
  }
}

function distinct(places: readonly Place<any>[], what: string): Place<any>[] {
  if (places.length === 0) throw new Error(`OpenNetContract: ${what} names no place`);
  const byName = new Map<string, Place<any>>();
  for (const p of places) if (!byName.has(p.name)) byName.set(p.name, p);
  return [...byName.values()];
}
