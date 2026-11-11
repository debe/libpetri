/**
 * App entry, bundled into the page's last `<script>`. Loads and decodes the data once, builds
 * the shell, routes, and mounts one view at a time.
 *
 * Owner: skeleton (core). View agents never edit this file.
 *
 * On each route: close overlays, dispose the old view, render the new one (a throwing view
 * becomes an error card; the shell stays usable), set `document.title`, announce the title,
 * move focus to the view's h1 (or `ViewResult.focus`), scroll to the top.
 *
 * Signals for tests: `<html data-route="<view>">` after each render, and
 * `<div id="app" data-ready="true">` after the first.
 */
import { APP_ROOT_ID } from '../model.js';
import type { AppContext, ViewResult } from './context.js';
import { loadSiteData } from './data.js';
import { buildIndex } from './indexes.js';
import { installKeyboard } from './keyboard.js';
import { closeAllOverlays } from './overlay.js';
import { currentRoute, navigate, onRouteChange, type Route } from './router.js';
import { createShell } from './shell.js';
import { errorPanel } from './ui.js';
import { renderRoute } from './views.js';

export const SITE_TITLE = 'libpetri spec';

function start(): void {
  const root = document.getElementById(APP_ROOT_ID);
  if (root === null) return;

  let ctx: AppContext;
  try {
    const data = loadSiteData();
    const index = buildIndex(data);
    ctx = { data, index, render: (route) => renderRoute(ctx, route), navigate };
  } catch (error) {
    console.error(error);
    root.replaceChildren(errorPanel('The spec data could not be read', error));
    return;
  }

  const shell = createShell(ctx);
  root.replaceChildren(shell.root);

  let current: ViewResult | null = null;
  let first = true;

  const show = (route: Route): void => {
    closeAllOverlays();
    try {
      current?.dispose?.();
    } catch (error) {
      console.error(error);
    }
    let view: ViewResult;
    try {
      view = ctx.render(route);
    } catch (error) {
      console.error(error);
      view = { title: 'Error', node: errorPanel('This view failed to render', error) };
    }
    current = view;
    shell.main.replaceChildren(view.node);
    shell.setRoute(route);
    document.title = view.title === SITE_TITLE ? SITE_TITLE : `${view.title} · ${SITE_TITLE}`;
    document.documentElement.dataset['route'] = route.view;
    if (!first) {
      window.scrollTo(0, 0);
      const target = view.focus ?? shell.main.querySelector<HTMLElement>('h1') ?? shell.main;
      target.focus({ preventScroll: true });
      shell.announce(view.title);
    }
    first = false;
  };

  onRouteChange(show);
  installKeyboard(ctx, () => shell.syncTheme());
  show(currentRoute());
  root.dataset['ready'] = 'true';
}

start();
