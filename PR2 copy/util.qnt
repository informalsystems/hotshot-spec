// -*- mode: Bluespec; -*-

/*
dummy change
This is done to trick github's rename detection algorithm
*/
module utils {
    import types.* from "./typeDef"
    import communication.* from "./comm"
    import basicSpells.* from "spells/basicSpells"
    import rareSpells.* from "spells/rareSpells"


    pure def certOrNeg(cert: Option[Certificate]): Certificate = {
        match(cert){
            |None => {which: Quorum, signers: Set(), nextEpochSigners: Set(),view: -1, block: -1}
            |Some(c) => c
        }
    }

    
    pure def listContains2(l: List[Block], block: Block): bool = {
        l.foldl(false, (acc, b) => acc or (b == block))
    }

    pure def fetchProposal(cert:Certificate, propDA: Set[Proposal]): Option[Proposal] = {
        //return the proposal that has the certificate
        propDA.find(prop => ( prop.block == cert.block and prop.view == cert.view))
    }

    
    pure def updateHighQCMap(highQC: Certificate, archive: Block -> Certificate): Block -> Certificate = {
        val exist = archive.keys().contains(highQC.block)
        if (exist){
            val oldQC = archive.get(highQC.block)
            if (highQC.view > oldQC.view) archive.set(highQC.block, highQC)
            else archive
        } else {
            archive.put(highQC.block, highQC)
        }
    }

    pure def commitedBlocks(newDecidedQC: Certificate, oldDecidedQC: Certificate, archive: Block -> Certificate): List[Certificate] = {
        val formedBlocks = archive.keys().filter(b => (b > oldDecidedQC.block) and (b <= newDecidedQC.block))
        // sort by view number and return the list of blocks
        val keptCerts =formedBlocks.map(b => archive.get(b))
        val keptCertsList = keptCerts.fold(List(), (acc, c) => acc.append(c))
        sortList(keptCertsList, (a,b) => a.view < b.view)
    }

    
    // Update a node's state to a new view
    pure def updateToNewView(state: LocalState, newView: int): LocalState = {
        if (newView > state.view) {
            {...state, view: newView}
        } else {
            state
        }
    }
}
