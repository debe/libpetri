/**
 * What every view receives. Views are functions `(ctx, route) => ViewResult`; they build a
 * detached node and never touch the shell. The shell mounts the node, sets the title and
 * calls `dispose` before the next view.
 *
 * Owner: skeleton (core).
 */
import type { SiteData } from '../model.js';
import type { SiteIndex } from './indexes.js';
import type { NavigateOptions, Route, RouteOf, ViewName } from './router.js';

export interface ViewResult {
  /** Document title prefix, e.g. `CORE-001 Place Definition`. */
  readonly title: string;
  readonly node: Node;
  /** Element to focus after mounting; the shell focuses `<main>` when absent. */
  readonly focus?: HTMLElement;
  /** Removes listeners, timers and observers the view started. */
  readonly dispose?: () => void;
}

export interface AppContext {
  readonly data: SiteData;
  readonly index: SiteIndex;
  /** Renders any route to a detached view (selftest and previews use it). */
  readonly render: (route: Route) => ViewResult;
  readonly navigate: (route: Route, options?: NavigateOptions) => void;
}

export type ViewFn<V extends ViewName> = (ctx: AppContext, route: RouteOf<V>) => ViewResult;
