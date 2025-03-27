// -*- mode: Bluespec; -*-
module types {
    import basicSpells.* from "spells/basicSpells"

    //// **Type definitions**
    type Block = int   //TODO: only storing block height currently
    type Node = int
    type NodeState = Active | Inactive // node status: part of current epoch (active) or not (inactive)

    type CertificateType = Quorum | Extended   // type of certificate (quorum or extended)
    type ProposalType = CertificateType        // type of proposal (quorum or extended)
    type VoteType = CertificateType            // type of vote (quorum or extended)

    // QC = Quorum Certificate
    type Certificate = {which: CertificateType, signers: Set[int], nextEpochSigners:Set[int],view : int, block: Block}
    // Message Types
    type Vote = {sender: Node, which: VoteType, view: int, block: Block}             
    type Proposal = {sender: Node, which: ProposalType, view: int, block: Block, certificate: Certificate}
    
    //type Message = 
        //Vote({sender: Node, which: VoteType, view: int, block: Block})
        //|Proposal({sender: Node, which: ProposalType, view: int, block: Block, certificate: Certificate})
    //  Revise, this is only for protoyping
    type StakingTable = Set[int]


    //// **State variables** (mutable state of the system)
    type LocalState = {
        epoch: int, //TODO Is this necessary? based on the code, it seems like it can be calculated from block height  
        view: int,
        // TODO: Do we have an initial state for these, or do they have to be optional?
        highQC: Option[Certificate], // highest proposal known to be valid
        lockedQC: Option[Certificate], // locked proposal
        decidedQC: Option[Certificate], // decided proposal
        decidedQCArchive: List[Certificate], // decided proposals
        chain: List[Block], // chain of decided blocks
        proposals: Set[Proposal],
        votes: Set[Vote],
        proposalArchive: Set[Proposal],
        voteArchive: Set[Vote],
        //may be needed to accumulate votes 
        votesMap: (VoteType, Block, int, int) -> Set[Node], //(type, data, view, epoch) -> voters
        // Network buffer
        votesBuffer: Set[Vote],
        propsBuffer: Set[Proposal],
    }
    type ProtocolState = Node -> LocalState


    // TODO: I think for modeling purposes, it might be better to have sepearate state for the network that contains the buffers
    // type NetworkState = {
}
