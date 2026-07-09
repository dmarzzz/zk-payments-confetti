# T7 nullifier-query accounting correction

The concrete FRAME handler publishes `x`, `y = k + a*x`, and
`nf = H_nf(a)` for every honest signal. The earlier query numerator counted
direct candidate-secret probes to `H_a`, `H_e`, and `H_id`, but not direct
`H_nf` queries or the number of honest line points exposed.

Given one signal, an adversary that finds a preimage `a` of its nullifier
computes `k = y - a*x`. With `q_sig` independently sampled honest slopes and
`q_Nf` preimage probes, a conservative multi-target first-hit charge is
`q_Nf*q_sig/|F|`. Separately, two honest slopes may collide; two distinct line
points with a shared slope recover `k`, contributing a birthday term bounded
conservatively by `q_sig^2/|F|`.

`Zkpc.Games.frameWinProb_slopeReveal_eq_one` kernel-checks the limiting
calibration `H_nf(a)=a`: one signal then frames with probability one. This is
not the real random oracle, but proves slope hiding is essential and cannot be
replaced by direct-secret query accounting.

The corrected numerator is

`q_A + q_E + q_Id + q_Nf*q_sig + q_sig^2 + 1`,

where `+1` is blind guessing. Tighter collision constants are possible later;
the current expression is deliberately conservative and compositional.
