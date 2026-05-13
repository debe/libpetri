/**
 * Glue between the {@link mountSubnetPanel} component and the executor: tracks
 * the most recent {@link SubnetInstanceInfo}[] from a `subscribed` response,
 * wires breakpoint toggles to the executor's `userSetBreakpoint` /
 * `userClearBreakpoint` environment places, and refreshes the panel whenever
 * the breakpoint list changes (so the per-card toggle reflects current state).
 */

import type { BitmapNetExecutor } from 'libpetri';
import { el } from '../../dom/elements.js';
import * as p from '../places.js';
import { mountSubnetPanel } from '../../dom/components/subnet-panel.js';
import { findInstanceBreakpoint, generateBreakpointId } from './breakpoints.js';
import type { SubnetInstanceInfo, BreakpointConfig } from '../../protocol/index.js';

let currentInstances: readonly SubnetInstanceInfo[] = [];
let executorRef: BitmapNetExecutor | null = null;

/** Cache the executor — must be called once at startup. */
export function setSubnetPanelExecutor(executor: BitmapNetExecutor): void {
  executorRef = executor;
}

/** Replace the cached instances and re-render. Called from `t_on_subscribed`. */
export function setSubnetInstances(instances: readonly SubnetInstanceInfo[]): void {
  currentInstances = instances;
  refreshSubnetPanel();
  refreshInstanceDatalist(instances);
}

/** Re-render with the cached instances; safe to call repeatedly. */
export function refreshSubnetPanel(): void {
  const exec = executorRef;
  mountSubnetPanel(el.subnetPanel, currentInstances, {
    isBreakpointSet: (prefix) => findInstanceBreakpoint(prefix) !== undefined,
    onToggleBreakpoint: (prefix, on) => {
      if (!exec) return;
      if (on) {
        const bp: BreakpointConfig = {
          id: generateBreakpointId(),
          type: 'INSTANCE_TRANSITION',
          target: prefix,
          enabled: true,
        };
        exec.injectValue(p.userSetBreakpoint, bp);
      } else {
        const existing = findInstanceBreakpoint(prefix);
        if (existing) {
          exec.injectValue(p.userClearBreakpoint, existing.id);
        }
      }
    },
    onSelectFilter: (prefix) => {
      el.filterInstance.value = prefix;
      el.applyFilter.click();
    },
  });
}

function refreshInstanceDatalist(instances: readonly SubnetInstanceInfo[]): void {
  const datalist = document.getElementById('instance-options');
  if (!datalist) return;
  datalist.innerHTML = '';
  for (const inst of instances) {
    const opt = document.createElement('option');
    opt.value = inst.prefix;
    datalist.appendChild(opt);
  }
}
