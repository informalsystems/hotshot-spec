# hotshot-spec

A Quint specification of Epoch changes in the Hotshot consensus.

Test the system for deadlock issues:
    `quint run hotshotTimeout.qnt --invariant=deadlock --mbt --max-steps 400 --max-samples 100`




Generate a run where the All view changes occur based on QC received :
    `quint run hotshotTimeout.qnt --invariant=optimalRun --mbt --step=optimalStep --max-steps 400 --max-samples 100`

Generate a run where a viewSync interrupts the epoch change protocol:
    `quint run hotshotTimeout.qnt --invariant=timeoutEpochRun --mbt --max-steps 400 --max-samples 100`
