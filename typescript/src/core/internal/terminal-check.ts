/**
 * @internal EXEC-042 checks shared by composition and subnet instantiation.
 */
import type { PetriNet } from '../petri-net.js';

/**
 * @internal EXEC-042 composition rule: terminals are a property of the whole net, so a subnet
 * body that declares any is rejected by `compose` and `instantiate`, naming the place(s).
 * Scoped termination (ending one subnet instance) is not defined.
 */
export function rejectSubnetTerminals(body: PetriNet, subnetName: string, operation: string): void {
  if (body.terminals.size === 0) return;
  const names = [...body.terminals].map(p => `'${p.name}'`).join(', ');
  throw new Error(
    `${operation}: subnet '${subnetName}' declares terminal place(s) ${names}. Terminal places ` +
    `end the whole run and are a property of the composed net, not of a subnet body; declare ` +
    `them on the enclosing net instead (EXEC-042).`,
  );
}
