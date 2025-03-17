module types {

//// **Type definitions**
  type Block = int   //TODO: only storing block height currently
  type Node = int
  type NodeState = Active | Inactive // node status: part of current epoch (active) or not (inactive)
  
  type CertificateType = QuorumC | ExtendedC | NoneC        // type of certificate (quorum or extended)
  type ProposalType = QuorumP | ExtendedP | NoneP           // type of proposal (quorum or extended)
  type VoteType = QuorumV | ExtendedV | NoneV              // type of vote (quorum or extended)

  // QC = Quorum Certificate
  type Certificate = {which: CertificateType, signers: Set[int], view : int, block: Block}
  // Message Types
  type Vote = {sender: Node, which: VoteType, view: int, block: Block}             
  type Proposal = {sender: Node, which: ProposalType, view: int, block: Block, certificate: Certificate}
  

  //  Revise, this is only for protoyping
  type StakingTable = Set[int]


  //// **State variables** (mutable state of the system)
  type LocalState = {
    epoch: int, //TODO Is this necessary? based on the code, it seems like it can be calculated from block height  
    view: int,
    highQC: Certificate, // highest proposal known to be valid
    lockedQC: Certificate, // locked proposal
    //isActive: bool,
    //isLeader: bool,
    //leader: int,
    proposals: Set[Proposal],
    votes: Set[Vote],
    // might need to add fields to hold the votes in order to build the certificate
  }
  type ProtocolState = int -> LocalState
}