# HotShot Consensus Epoch Changes - Quint Specification

A Quint specification of Epoch changes in the Hotshot consensus.

<img src="artwork.png" width=50% height=50% alt="Quint Espresso Artwork">

Check out the blog post about this work: [Espresso HotShot Epoch Changes in Quint](https://informal.systems/blog/espresso-hotshot-epoch-changes-in-quint-2025)

## Usage

Test the system for deadlock issues:
``` sh
quint run hotshotTimeout.qnt --invariant=deadlock --max-steps 40 --max-samples 100
```

Generate a run where the all view changes occur based on QC received:
``` sh
quint run hotshotTimeout.qnt --invariant=optimalRun --step=stepWithoutTimeout --max-steps 40 --max-samples 100
```

Generate a run where a viewSync interrupts the epoch change protocol:
``` sh
quint run hotshotTimeout.qnt --invariant=timeoutEpochRun --max-steps 50 --max-samples 100
```

