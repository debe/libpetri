import Libpetri.Novel.Seam.Index
import Libpetri.Novel.Seam.Net
import Libpetri.Novel.Seam.Excuses
import Libpetri.Novel.Seam.Bad
import Libpetri.Novel.Seam.Sound
import Libpetri.Novel.Seam.Retrodict

/-!
# The name → index seam ([VER-001], [CORE-072])

Root of the `Novel/Seam/` modules, which model what `Basic.lean`'s `PlaceId := Nat` and
`proposition_one`'s seed `alpha m0` idealised away: the flat index is a finite list of declared
names (`Index.lean`), the named net and the inert-place rewrite (`Net.lean`), the error rule's
`Bad` per property arm (`Excuses.lean`, `Bad.lean`), the end-to-end soundness of a CHC `Proven`
(`Sound.lean`), and the stray-token `Proven` the idealisation let through (`Retrodict.lean`).
-/
