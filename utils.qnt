// -*- mode: Bluespec; -*-

module utils {
  import types.* from "./types"
  import communication.* from "./communication"
  import basicSpells.* from "spells/basicSpells"
  import rareSpells.* from "spells/rareSpells"

  pure def certOrNeg(cert: Option[Certificate]): Certificate = {
    match(cert) {
       | None => { cType: Quorum, signers: Set(), nextEpochSigners: Set(), view: -1, block: -1 }
       | Some(c) => c
    }
  }

  /// Returns the proposal that has the certificate
  pure def fetchProposal(cert: Certificate, propDA: Set[Proposal]): Option[Proposal] = {
    propDA.find(prop => prop.block == cert.block and prop.view == cert.view)
  }

  pure def updateHighQCMap(highQC: Certificate, archive: Block -> Certificate): Block -> Certificate = {
    archive.setByWithDefault(
      highQC.block,
      cert => if (highQC.view > cert.view) highQC else cert,
      highQC
    )
  }

  pure def commitedBlocks(newDecidedQC: Certificate, oldDecidedQC: Certificate, archive: Block -> Certificate): List[Certificate] = {
    val formedBlocks = archive.keys().filter(b => b > oldDecidedQC.block and b <= newDecidedQC.block)
    // Sort by view number and return the list of blocks
    val keptCerts = formedBlocks.map(b => archive.get(b))
    keptCerts.toList((a, b) => intCompare(a.view, b.view))
  }
}
