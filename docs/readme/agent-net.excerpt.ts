import {
  PetriNet, Transition, forwardInput, one, outPlace, place, timeout, transformFrom, xor,
} from 'libpetri';

type Turn = { question: string; notes: string[] };
type Reply = { tool: string } | { answer: string };

const request = place<string>('request');
const thinking = place<Turn>('thinking');
const toolCall = place<Turn>('toolCall');
const toolResult = place<{ turn: Turn; result: string }>('toolResult');
const toolBudget = place<null>('toolBudget');   // k permits, never refunded
const answer = place<string>('answer');
const failed = place<Turn>('failed');

function agentTurn(model: (t: Turn) => Promise<Reply>, tool: (t: Turn) => Promise<string>) {
  const start = Transition.builder('start')
    .inputs(one(request)).outputs(outPlace(thinking))
    .action(transformFrom(request, question => ({ question, notes: [] })))
    .build();
  const callModel = Transition.builder('call-model')
    .inputs(one(thinking)).outputs(xor(outPlace(toolCall), outPlace(answer)))
    .action(async ctx => {
      const turn = ctx.input(thinking), reply = await model(turn);
      if ('answer' in reply) ctx.output(answer, reply.answer);
      else ctx.output(toolCall, { ...turn, notes: [...turn.notes, `call ${reply.tool}`] });
    })
    .build();
  const runTool = Transition.builder('run-tool')
    .inputs(one(toolCall), one(toolBudget))
    .outputs(xor(outPlace(toolResult), timeout(10_000, forwardInput(toolCall, thinking))))
    .action(async ctx => {
      const turn = ctx.input(toolCall);
      ctx.output(toolResult, { turn, result: await tool(turn) });
    })
    .build();
  const observe = Transition.builder('observe')
    .inputs(one(toolResult)).outputs(outPlace(thinking))
    .action(transformFrom(toolResult, ({ turn, result }) => ({ ...turn, notes: [...turn.notes, result] })))
    .build();
  const giveUp = Transition.builder('give-up')       // the fix: budget spent, stop
    .inputs(one(toolCall)).inhibitor(toolBudget).outputs(outPlace(failed))
    .action(transformFrom(toolCall, turn => turn))
    .build();
  return PetriNet.builder('agent-turn')
    .transitions(start, callModel, runTool, observe, giveUp).build();
}
