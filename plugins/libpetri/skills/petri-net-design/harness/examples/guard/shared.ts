/** Pieces both guard candidates share: the guard subnet and the turn front end. */
import { SubnetDef, Transition, one, outPlace, place, xorPlaces, type Place } from 'libpetri';

export const p = (name: string): Place<unknown> => place<unknown>(name);

/** Checks the input and reports a verdict on OK or BAD. */
export function guard(): SubnetDef<void> {
  const IN = p('IN'), CHECKING = p('CHECKING'), OK = p('OK'), BAD = p('BAD');
  return SubnetDef.builder('Guard')
    .place(IN).place(CHECKING).place(OK).place(BAD)
    .transition(Transition.builder('start').inputs(one(IN)).outputs(outPlace(CHECKING)).build())
    .transition(Transition.builder('verdict').inputs(one(CHECKING)).outputs(xorPlaces(OK, BAD)).build())
    .inputPort('in', IN).outputPort('ok', OK).outputPort('bad', BAD)
    .build();
}

/** Host places, by name, used by both candidates. */
export function hostPlaces() {
  return {
    SOURCE: p('SOURCE'), INBOX: p('INBOX'), TURN_PERMIT: p('TURN_PERMIT'),
    G_IN: p('G_IN'), A_IN: p('A_IN'), VERDICT_OK: p('VERDICT_OK'), VERDICT_BAD: p('VERDICT_BAD'),
    DRAFT: p('DRAFT'), SENT: p('SENT'), REFUSED: p('REFUSED'),
  };
}

export function marking(k: number): ReadonlyMap<string, number> {
  return new Map([['SOURCE', k], ['TURN_PERMIT', 1]]);
}
