// -*- mode: Bluespec; -*-
module types {
  import basicSpells.* from "spells/basicSpells"

  type Block = int // We only need to store the block height
  type Node = int

  type CertificateType = Quorum | Extended   // type of certificate (quorum or extended)
  type ProposalType = CertificateType        // type of proposal (quorum or extended)
  type VoteType = CertificateType            // type of vote (quorum or extended)

  type Certificate = {
    cType: CertificateType,
    signers: Set[int],
    nextEpochSigners:Set[int],
    view : int,
    block: Block
  }

  // Message Types
  type Vote = { sender: Node, vType: VoteType, view: int, block: Block }
  type Proposal = { sender: Node, pType: ProposalType, view: int, block: Block, certificate: Certificate }

  type MessageContent = ProposalMessage(Proposal) | VoteMessage(Vote)
  type Message = { destinatary: Node, message: MessageContent }

  /// Staking table representation.
  type StakingTable = Set[int]

  /// State of a single Node/Validator/Replica in the System.
  type LocalState = {
    node: Node,
    view: int,
    // QC = Quorum Certificate
    highQC: Option[Certificate], // Highest proposal known to be valid
    lockedQC: Option[Certificate], // Locked proposal
    decidedQC: Option[Certificate], // Decided proposal
    decidedQCArchive: List[Certificate], // Decided proposals
    chain: int -> List[Block],
    highQCArchive : Block -> Certificate,
    proposalArchive: Set[Proposal], // Keep track of all the received proposals
    voteArchive: Set[Vote], // Keep track of all the received votes
    votesMap: (VoteType, Block, int, int) -> Set[Node], // (type, data, view, epoch) -> voters
  }

  /// Protocol State is a mapping from a node ID to individual node states.
  type ProtocolState = Node -> LocalState
}
