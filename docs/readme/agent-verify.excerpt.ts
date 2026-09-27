import { SmtVerifier, deadlockFree } from 'libpetri/verification';

function verifyTurn(net: PetriNet) {
  return SmtVerifier.forNet(net)
    .initialMarking(m => m.tokens(request, 1).tokens(toolBudget, 2))
    .property(deadlockFree())
    .sinkPlaces(answer, failed, toolBudget)   // unspent permits may remain
    .verify();
}
