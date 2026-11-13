import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.ENV_002
import Libpetri.Spec.Text.EVT_013
import Libpetri.Spec.Text.EXEC_002
import Libpetri.Spec.Text.IO_015
import Libpetri.Spec.Text.MOD_024
import Libpetri.Spec.Text.TIME_015
import Libpetri.Spec.Text.VER_013

/-! The divergence table of the runtime ledger, one row per command, in table order. Python binds
the Rust crate, so it follows the Rust column unless a cell says otherwise. -/

ledger_divergence "Bitmap word size"
  spec "not specified"
  java "64-bit (`long`)"
  typescript "32-bit (`Uint32Array`)"
  rust "64-bit (`u64`)"

ledger_divergence "Concurrency model"
  spec "single-threaded orchestrator"
  java "actions invoked inline; concurrency comes from the returned stage"
  typescript "Promise microtasks"
  rust "Tokio async tasks"

ledger_divergence "Place equality ([MOD-024])"
  spec "implementation's own"
  java "structural on name and token type; restore takes the net's places"
  typescript "name only"
  rust "name only"

ledger_divergence "Token type safety"
  spec "typed places and tokens"
  java "generics (compile time)"
  typescript "phantom type parameter"
  rust "generics (compile time)"

ledger_divergence "Inject into an unregistered place ([ENV-002])"
  spec "error for a handle-taking inject"
  java "failed future"
  typescript "rejects; `injectNoAwait` throws"
  rust "deposited into the named place; registration is the host's"

ledger_divergence "Enablement-timestamp resolution ([EXEC-002] AC3)"
  spec "sub-ms precision kept"
  java "monotonic `long` nanoseconds"
  typescript "float milliseconds"
  rust "float milliseconds"

ledger_divergence "Injectable clock seam ([TIME-015])"
  spec "host-supplied clock"
  java "`ExecutionEnvironment`"
  typescript "`Clock`"
  rust "`ExecutorClock`; Python offers only the Rust-side `ManualClock` and `SteppedClock`"

ledger_divergence "Mid-action publication ([IO-015])"
  spec "optional"
  java "none"
  typescript "none"
  rust "`ctx.flush()`; flushed tokens survive a later validation failure"

ledger_divergence "Inline synchronous execution"
  spec "not specified"
  java "none"
  typescript "none"
  rust "`try_run_inline`"

ledger_divergence "Action binding"
  spec "separate from structure"
  java "`bindActions`"
  typescript "`bindActions`"
  rust "`NetStructureBuilder`"

ledger_divergence "Log capture ([EVT-013])"
  spec "action log becomes events"
  java "SLF4J `LogCaptureScope`"
  typescript "`ctx.log()`"
  rust "`ctx.log()`"

ledger_divergence "Verification cancellation ([VER-013])"
  spec "shares the total budget's stop"
  java "thread interruption, flag restored"
  typescript "`AbortSignal`"
  rust "`CancelToken` (Python `libpetri.CancelToken`)"
