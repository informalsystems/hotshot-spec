// -*- mode: Bluespec; -*-
module types {
    import basicSpells.* from "spells/basicSpells"

    //// **Type definitions**
    type Block = int   //only storing block height currently
    type Node = int

    type CertificateType = Quorum | Extended   // type of certificate (quorum or extended)
    type ProposalType = CertificateType        // type of proposal (quorum or extended)
    type VoteType = CertificateType            // type of vote (quorum or extended)

    /// QC = Quorum Certificate
    type Certificate = {cType: CertificateType, signers: Set[int], nextEpochSigners:Set[int],view : int, block: Block}
    
    // Message Types
    type Vote = {sender: Node, vType: VoteType, view: int, block: Block}             
    type Proposal = {sender: Node, pType: ProposalType, view: int, block: Block, certificate: Certificate}
    type Timeout = {sender: Node, view: int, latestCertificate: Certificate}
    
    /// Staking table representation.
    type StakingTable = Set[int]


    //// **State variables**
    
    /// State of a single Node/Validator/Replica in the System.
    type LocalState = {
        view: int,
        highQC: Option[Certificate], // highest proposal known to be valid
        lockedQC: Option[Certificate], // locked proposal
        decidedQC: Option[Certificate], // decided proposal
        decidedQCArchive: List[Certificate], // decided proposals
        chain: int -> List[Block],
        highQCArchive : Block -> Certificate,
        proposalArchive: Set[Proposal], //keeping track of all the received proposal
        voteArchive: Set[Vote], //keeping track of all the received votes
        votesMap: (VoteType, Block, int, int) -> Set[Node], //(type, data, view, epoch) -> voters
        // Message buffer
        votesBuffer: Set[Vote],
        propsBuffer: Set[Proposal],
    }
    /// Protocol State is a mapping from a node ID to individual node states.
    type ProtocolState = Node -> LocalState

}
