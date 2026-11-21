import Deadlock.Orphan
open Deadlock Deadlock.Orphan
#eval render { orphanDesc with templates := [tR, { tC with supervisor := none }, tG] }
#eval render { orphanDesc with templates := [tR, tC, { tG with tombstone := "" }] }
