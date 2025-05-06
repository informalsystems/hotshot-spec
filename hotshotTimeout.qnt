// -*- mode: Bluespec; -*-
module HotShotEpochReconfig {
  import types.* from "./types"
  import utils.* from "./utils"

  import communication.* from "./communication"

  import basicSpells.* from "spells/basicSpells"
  import commonSpells.* from "spells/commonSpells"
  import rareSpells.* from "spells/rareSpells"

  /* Constants (system parameters) */

  /// Number of participants in every consensus epoch, we assume that the number of particpants per epoch is constant.
  const N: int
  /// Fault tolerance threshold per epoch.
  const F: int
  /// Quorum size (2F+1 signatures needed for decisions)
  const Q: int
  /// Epoch duration
  const K: int
  /// Size of the universe of node IDs (>= N, to allow new nodes joining/leaving)
  const MAX_NODES: int
  /// Set of faulty nodes (size <= F)
  const FAULTY: Set[Node]
  /// List of validators for each epoch, each entry is a list of node IDs.
  /// the Node at index (j,i) is the leader of view i in epoch j (modulo the length of the list[j]).
  /// The first 2 views should be led by the node 1 to be compatible with our current initialization.
  const VALIDATORS: List[List[Node]]

  pure val allNodes = 1.to(MAX_NODES)
  pure val correct: Set[Node] = allNodes.exclude(FAULTY)

  /// A set representation of the validators for each epoch.
  pure val stakingTables: List[StakingTable] = {
    VALIDATORS.listMap(l => l.toSet())
  }

  pure val allFaultyMessages: Set[Message] = {
    pure val allFaultyVotes: Set[Vote] = Set()
    pure val allFaultyProposals: Set[Proposal] = Set()

    tuples(correct, allFaultyVotes)
      .map(((node, vote)) => { destinatary: node, message: VoteMessage(vote) })
      .union(
        tuples(correct, allFaultyProposals)
        .map(((node, prop)) => { destinatary: node, message: ProposalMessage(prop) })
      )
  }

  /* Initial State Values */

  pure val genesisCert = {
    cType: Quorum,
    signers: stakingTables[0], // Genesis block is signed by all nodes in the first epoch
    nextEpochSigners: Set(),
    view: 0,
    block: 0
  }

  pure val genesisProp = {
    sender: 1,
    pType: Quorum,
    view: 1,
    block: 1,
    certificate: genesisCert
  }

  /// Initialize the state of the system
  pure val initState: ProtocolState = {
    1.to(MAX_NODES).mapBy(node => {
      node: node,
      view: 0,
      highQC: None,
      highQCArchive: Map(),
      lockedQC: None,
      decidedQC: None,
      chain: Map(),
      decidedQCArchive: List(),
      proposalArchive: Set(),
      voteArchive: Set(),
      votesMap: Map(),
    })
  }

  /* State Variables */

  /// The state of the protocol is represented as a map from node IDs to local states
  var protocolState: ProtocolState

  /// Messages in transit (to be delivered)
  var messages: Set[Message]

  /* Functions */

  /// Check if a node is part of the staking table for a given epoch
  pure def isInEpoch(node: Node, epoch: int): bool = {
    val epochIndex = (epoch - 1) % length(stakingTables)
    if (epoch <= 0) false
    else stakingTables[epochIndex].contains(node)
  }

  /// Return the leader for a given view and epoch
  pure def leader(view: int, epoch: int): int = {
    val leaders = VALIDATORS
    val epochIndex = (epoch - 1) % length(leaders)
    val viewIndex = view % length(leaders[epochIndex])
    leaders[epochIndex][viewIndex]
  }

  /// Check if a block is the last block of the epoch
  pure def isLastBlockOfEpoch(block: int): bool = {
    block % K == 0
  }

  /// Check if a block is the first block of the epoch
  pure def isFirstBlockOfEpoch(block: int): bool = {
    block % K == 1
  }

  /// Return the epoch for a given block height
  pure def blockEpoch(block: int): int = {
    if (block.isLastBlockOfEpoch()) block / K else block / K + 1
  }

  /// Return the epochs for which a node is active (only the current epoch or the current and next epoch)
  pure def getEpochs(node: Node, block: Block): Set[int] = {
    val epoch = block.blockEpoch()

    if (block.isLastBlockOfEpoch())
      Set(epoch, epoch + 1).filter(e => node.isInEpoch(e))
    else
      Set(epoch).filter(e => node.isInEpoch(e))
  }

  /// Check if a node is the leader for a given view and block
  pure def isLeader(node: Node, view: int, block: int): bool = {
    node == leader(view, block.blockEpoch())
  }

  /// Abstraction of signature validation
  pure def isSignatureValid: bool = {
    true
  }

  /// Check if a received vote is valid for a given node
  pure def isVoteValid(vote: Vote, state: LocalState): bool = {
    pure val epoch = vote.block.blockEpoch()
    pure val validSignature = isSignatureValid

    and {
      vote.view >= state.view,
      validSignature,
      if (vote.block.isLastBlockOfEpoch()) and {
        vote.vType != Extended implies state.node.isLeader(vote.view + 1, vote.block),
        state.node.isInEpoch(epoch) or state.node.isInEpoch(epoch + 1),
      } else and {
        state.node.isLeader(vote.view + 1, vote.block),
        state.node.isInEpoch(epoch),
      }
    }
  }

  /// Abstraction tailored for simple simulations
  pure def extends(a: Block, b: Block): bool = {
    a > b
  }

  /// Return a proposal record
  pure def proposal(
    node: Node,
    block: Block,
    view: int,
    pType: ProposalType,
    cert: Certificate
  ): Proposal = {
    { sender: node, pType: pType, view: view, block: block, certificate: cert }
  }

  /// Return a vote record
  pure def vote(node: Node, block: Block, view: int, vType: VoteType): Vote = {
    { sender: node, vType: vType, view: view, block: block }
  }

  /// Return a certificate record for a given block, includes optional extra
  /// signers for the next epoch if the block is the last of the current epoch
  pure def certificate(
    node: Node,
    cType: CertificateType,
    view: int,
    block: Block,
    state: LocalState
  ): Certificate = {
    pure val epoch = block.blockEpoch()
    pure val signers = state.votesMap.getOrElse((cType, block, view, epoch), Set())
    pure val nextEpochSigners = if (block.isLastBlockOfEpoch()) {
      state.votesMap.getOrElse((cType, block, view, epoch + 1), Set())
    } else {
      Set()
    }

    {
      cType: cType,
      signers: signers,
      nextEpochSigners: nextEpochSigners,
      view: view,
      block: block
    }
  }

  /// Form a proposal based on a certificate.
  pure def formProposal(cert: Certificate, state: LocalState): Proposal = {
    if (cert.block % K == 0 and cert.block > 0) {
      // Last block of the epoch
      match cert.cType {
        | Extended => {
          // Propose the first block of the next epoch
          pure val newBlock = cert.block + 1
          proposal(state.node, newBlock, state.view, Quorum, cert)
        }
        | Quorum => {
          // Propose the same block until the epoch reconfiguration is done
          pure val newBlock = cert.block

          // Determine the type of the proposal based on the highQC and lockedQC, is the 3 chain condition met?
          pure val newPropType = if (state.highQC != None and state.lockedQC != None) {
            pure val highQC = state.highQC.unwrap()
            pure val lockedQC = state.lockedQC.unwrap()

            if (highQC.block == lockedQC.block and
                state.view - 1 == highQC.view and
                highQC.view - 1 == lockedQC.view)
              Extended
            else
              Quorum
          } else {
            // If the QCs are not set, the extended proposal cannot be formed
            Quorum
          }

          pure val newView = state.view
          proposal(state.node, newBlock, newView, newPropType, cert)
        }
      }
    } else {
      // Not the last block of the epoch, propose the next block
      pure val newBlock = cert.block + 1
      proposal(state.node, newBlock, state.view, Quorum, cert)
    }
  }

  /// Check if the proposal respects the safety and liveness properties
  pure def isProposalSafe(proposal: Proposal, state:LocalState): bool = {
    pure val lockedQC = state.lockedQC
    pure val block = proposal.block

    match (lockedQC) {
      | None => true // No locked QC, the proposal is safe by default (TODO: Is this correct?)
      | Some(qc) => {
        or {
          block.extends(qc.block), // Safety
          proposal.certificate.view > qc.view // Liveness
        }
      }
    }
  }

  /// Check if the certificate included in the proposal is valid
  pure def isCertValid(proposal: Proposal, state: LocalState): bool = {
    pure val cert = proposal.certificate
    pure val block = proposal.block
    pure val epoch = block.blockEpoch()

    if (block.isLastBlockOfEpoch()) {
      and {
        cert.cType != Extended,

        // Check if the proposal with the repeated block (ie part of epoch
        // change) has enough signatures for the current and next epoch
        (block == cert.block) implies and {
          size(cert.signers.filter(s => s.isInEpoch(epoch))) >= Q ,
          size(cert.nextEpochSigners.filter(s => s.isInEpoch(epoch + 1))) >= Q
        },

        // Proposal uses cerificate with block K-1, need to be signed only by nodes in epoch e.
        (block != cert.block) implies and {
          isProposalSafe(proposal, state),
          size(cert.signers.filter(s => s.isInEpoch(epoch))) >= Q
        }
      }
    } else if (block.isFirstBlockOfEpoch() and block != 1) {
      // First block of the epoch and not the genesis block, special treatment
      // for the first block to ensure the system starts progressing
      and {
        cert.cType == Extended,
        isProposalSafe(proposal, state),
        size(cert.signers) >= Q,
        size(cert.nextEpochSigners) >= Q,
      }
    } else {
      // Not first or last block of the epoch
      and {
        cert.cType != Extended,
        isProposalSafe(proposal, state),
        size(cert.signers.filter(s => s.isInEpoch(epoch))) >= Q
      }
    }
  }

  pure def isExtendedProposalValid(proposal: Proposal, state: LocalState): bool = and {
    state.highQC != None,
    pure val highQC = state.highQC.unwrap()

    or {
      and {
        // This is a trick to avoid a node updating it's QC and rejecting it's own proposal
        proposal.sender == state.node,
        proposal.block == proposal.certificate.block,
        proposal.block == highQC.block,
        proposal.view - 1 == proposal.certificate.view,
        proposal.certificate.view == highQC.view
      },
      and {
        proposal.block == proposal.certificate.block,
        proposal.block == highQC.block,
        proposal.view - 1 == proposal.certificate.view,
        proposal.certificate.view - 1 == highQC.view
      }
    }
  }

  pure def isProposalValid(state: LocalState, proposal: Proposal): bool = {
    and {
      proposal.view >= state.view,
      isSignatureValid,
      isLeader(proposal.sender, proposal.view, proposal.block),
      proposal.pType == Extended implies isExtendedProposalValid(proposal, state),
      isCertValid(proposal, state),
    }
  }

  /// Utility function to update the stored chain
  pure def updateChain(
    node: Node,
    oldChain: int -> List[Block],
    newBlocks: List[Certificate]
  ): int -> List[Block] = {
    pure val chainMap = newBlocks.foldl(oldChain, (cm, c) => {
      pure val epoch = c.block / K + 1
      pure val x = cm.has(epoch)
      if (x)
        cm.setBy(epoch, chain => chain.append(c.block))
      else
        cm.put(epoch, List(c.block))
    })
    pure val goodEpochs = chainMap.keys().filter(e => not(node.isInEpoch(e)))
    chainMap.mapRemoveAll(goodEpochs)
  }

  /// Update the stored quorum certificates (high-locked-decided) in the local
  /// state based on the last observed valid certificate and commit the
  /// decided blocks to the chain.
  pure def updateCerts(
    oldState: LocalState,
    cert: Certificate,
    allProps: Set[Proposal]
  ): LocalState = {
    pure val highQC = cert
    pure val state = {
      ...oldState,
      highQC: Some(highQC),
      highQCArchive: updateHighQCMap(highQC, oldState.highQCArchive),
    }

    // TODO: This is a hack, did this to avoid  having many nested match statements
    pure val lockedQC = certOrNeg(state.lockedQC)
    pure val decidedQC = certOrNeg(state.decidedQC)

    pure val justifyHighP = fetchProposal(highQC, allProps)
    match justifyHighP {
      | None => state
      | Some(p) => {
        pure val justifyHighQC = p.certificate
        pure val justify2HighP = fetchProposal(justifyHighQC, allProps)
        match justify2HighP {
          | None => state
          | Some(p2) => {
            pure val justify2HighQC = p2.certificate
            pure val updateLockedQC = and {
              highQC.view - 1 == justifyHighQC.view,
              justifyHighQC.view > lockedQC.view
            }
            pure val updateDecidedQC = and {
              justifyHighQC.view - 1 == justify2HighQC.view,
              justify2HighQC.view > decidedQC.view
            }

            if (updateLockedQC and updateDecidedQC) {
              // The last block of the epoch is commited by the nodes of epoch+1
              pure val newBlocks = commitedBlocks(justify2HighQC, decidedQC, state.highQCArchive)

              { ...state,
                highQC: Some(highQC),
                lockedQC: Some(justifyHighQC),
                decidedQC: Some(justify2HighQC),
                highQCArchive: state.highQCArchive.mapRemoveAll(newBlocks.toSet().map(c => c.block)),
                chain: updateChain(state.node, state.chain, newBlocks)
              }
            } else if (updateLockedQC) {
              { ...state, highQC: Some(highQC), lockedQC: Some(justifyHighQC) }
            } else if (updateDecidedQC) {
              pure val newBlocks = commitedBlocks(justify2HighQC, decidedQC, state.highQCArchive)

              { ...state,
                highQC: Some(highQC),
                decidedQC: Some(justify2HighQC),
                highQCArchive: state.highQCArchive.mapRemoveAll(newBlocks.toSet().map(c => c.block)),
                chain: updateChain(state.node, state.chain, newBlocks),
              }
            } else {
              { ...state, highQC: Some(highQC)}
            }
          }
        }
      }
    }
  }

  /// Update the node's Votes Map with the new vote
  pure def accumulateSignatures(vote: Vote, state: LocalState): LocalState = {
    pure val epochs = getEpochs(vote.sender, vote.block)

    // For each relevant epoch, add the voter to the votes map
    pure val newVotes = epochs.fold(state.votesMap, (newVotesMap, e) => {
      pure val key = (vote.vType, vote.block, vote.view, e)
      newVotesMap.setByWithDefault(
        key,
        voters => voters.union(Set(vote.sender)).filter(n => n.isInEpoch(e)),
        Set()
      )
    })

    { ...state, votesMap: newVotes }
  }

  /// Check if a quorum of votes has been reached for a proposal based on the accumulated votes
  pure def thresholdReached(vote: Vote, state: LocalState): bool = {
    pure val epochs = if (vote.block % K == 0)
      Set(vote.block / K, vote.block / K + 1)
    else
      Set(vote.block / K + 1)

    // For each relevant epoch, check if we have enough votes
    epochs.forall(e => {
      pure val key = (vote.vType, vote.block, vote.view, e)
      pure val voters = state.votesMap.getOrElse(key, Set())
      voters.size() >= Q
    })
  }

  /// Send a proposal to the leader (either the current leader or the next epoch leader)
  pure def sendVoteToLeader(state: LocalState, vote: Vote): Set[Message] = {
    pure val epoch = if (vote.block % K == 0) vote.block / K else vote.block / K + 1

    pure val leaderToSend = if (vote.vType == Extended) {
      leader(state.view + 1, epoch + 1)
    } else {
      leader(state.view + 1, epoch)
    }

    sendVote(leaderToSend, vote)
  }

  /// Handle a vote message by updating the local state of the node and possibly sending a proposal.
  pure def handleVote(vote: Vote, oldState: LocalState, allProps: Set[Proposal]): (LocalState, Set[Message]) = {
    pure val state = {
      ...oldState,
      voteArchive: oldState.voteArchive.union(Set(vote))
    }
    pure val epoch = vote.block.blockEpoch()

    if (isVoteValid(vote, state)) {
      pure val stateWithSig = accumulateSignatures(vote, state)

      if (thresholdReached(vote, stateWithSig)) {
        // Form a certificate
        pure val cert = certificate(state.node, vote.vType, vote.view, vote.block, stateWithSig)
        pure val stateWithCerts = updateCerts(stateWithSig, cert, allProps)
        pure val newView = cert.view + 1
        pure val newState = { ...stateWithCerts, view: newView }

        // This is a trick to avoid duplicating the code from formProposal,
        // We use the "potential" new proposal to check if we have passed to the next epoch or not
        pure val newProp = formProposal(cert, newState)
        pure val newPropEpoch = newProp.block.blockEpoch()

        if (state.node == leader(newProp.view, newPropEpoch)) {
          // Update certificates based on the proposal's certificate
          pure val receivers = if (isLastBlockOfEpoch(newProp.block)) {
            // If the proposal is the last block of the epoch, send to all nodes in the current and next epoch
            allNodes.filter(n => n.isInEpoch(newPropEpoch) or n.isInEpoch(newPropEpoch + 1))
          } else {
            allNodes.filter(n => n.isInEpoch(newPropEpoch))
          }

          (newState, multicastProposal(receivers, newProp))
        } else {
          (newState, Set())
        }
      } else {
        // Do nothing
        (stateWithSig, Set())
      }
    } else {
      // Do nothing
      (state, Set())
    }
  }

  /// Handle a proposal message by updating the local state of the node and possibly sending a vote.
  pure def handleProposal(
    prop: Proposal,
    oldState: LocalState,
    allProps: Set[Proposal]
  ): (LocalState, Set[Message]) = {
    pure val state = {
      ...oldState,
      proposalArchive: oldState.proposalArchive.union(Set(prop)),
    }

    if (isProposalValid(state, prop)) {
      pure val stateWithCerts = updateCerts(state, prop.certificate, allProps)
      pure val newState = { ...stateWithCerts, view: prop.view }
      pure val newVote = vote(state.node, prop.block, prop.view, prop.pType)

      if (prop.pType == Extended) {
        // if the prop is an extended vote
        pure val receivers = allNodes.filter(n => n.isInEpoch(prop.block / K + 1))
        (newState, multicastVote(receivers, newVote))
      } else {
        (newState, sendVoteToLeader(newState, newVote))
      }
    } else {
      (state, Set())
    }
  }


  /// Get the highest view number among all correct nodes
  pure def getHighestView(pState: ProtocolState): int = {
    correct.fold(0, (maxView, node) => max(pState.get(node).view, maxView))
  }

  /* Actions */

  /// Utility function to accumulate all proposals from the protocol state.
  /// Used to simulate fetchProposal from network.
  val allProposals = {
    val archivedProposals = protocolState.values().fold(Set(), (props, state) => {
      props.union(state.proposalArchive)
    })
    messages.getProposals().union(archivedProposals)
  }

  val activeNodes = protocolState.keys()

  /// This action abstracts away viewSync and brings all correct nodes to the highest view
  action viewSync: bool = {
    // find the highest view among all correct nodes
    val highestView = getHighestView(protocolState)
    val nodes = protocolState.keys()

    // update the state of all nodes to the highest view
    val updatedState = nodes.fold(protocolState, (pState, node) => {
      pState.setBy(node, s => { ...s, view: max(s.view, highestView) })
    })

    // leader collects the highest QC from all correct nodes
    val highestQC = correct.fold(genesisCert, (maxQC, node) => {
      val nodeQC = updatedState.get(node).highQC
      match(nodeQC) {
        | None => maxQC
        | Some(qc) => {
          if (qc.block > maxQC.block) qc else maxQC
        }
      }
    })

    val lastCertifiedBlock = highestQC.block
    val epoch = lastCertifiedBlock.blockEpoch()
    all {
      epoch > 0,

      // leader of the next view proceeds to propose a new block
      val newLeader = leader(highestView + 1, epoch)
      // update the view of the new leader
      val newLeaderState = { ...updatedState.get(newLeader), view: highestView + 1 }

      // form a new proposal
      val newProp0 = formProposal(highestQC, newLeaderState)
      // if the new proposal is an extended proposal, restart the 3 successive certs procedure
      val newProp = if (newProp0.pType == Extended) {
        proposal(newLeader, highestQC.block, highestView + 1, Quorum, highestQC)
      } else {
        newProp0
      }

      val newPropEpoch = newProp.block.blockEpoch()
      val receivers = if (newProp.block.isLastBlockOfEpoch()) {
        nodes.filter(n => n.isInEpoch(newPropEpoch) or n.isInEpoch(newPropEpoch + 1))
      } else {
        nodes.filter(n => n.isInEpoch(newPropEpoch))
      }

      val newMessages = multicastProposal(receivers, newProp)

      all {
        protocolState' = updatedState.set(newLeader, newLeaderState),
        messages' = messages.union(newMessages),
      }
    }
  }

  /// Initialize the state of the system
  action init = all {
    protocolState' = initState,
    messages' = correct.map(n => { destinatary: n, message: ProposalMessage(genesisProp) }),
  }

  /// Execution Loop
  /// The execution step (step) either:
  /// Delivers a subset of the pending messages.
  /// Triggers a viewSync.
  action step = {
    // Nondeterministically choose between normal message handling and view
    // synchronization with a skew towards normal steps so the system is more
    // likely to make progress
    pure val odds = 1.to(100)
    nondet timeout = oneOf(odds)

    // The view sync occurs with a probabiliy of 1%
    if (timeout == 1) {
      viewSync
    } else {
      stepWithoutTimeout
    }
  }

  /// Execution step without viewSync
  action stepWithoutTimeout = {
    nondet n = oneOf(correct)
    val state = protocolState.get(n)

    val messagesToActive = messages.union(allFaultyMessages)
      .filter(m => m.destinatary.in(activeNodes))

    nondet messagesToReceive = oneOf(messagesToActive.powerset())
    val updatedMessages = messages.exclude(messagesToReceive)
    val accumulatedResult = messagesToReceive.fold((protocolState, updatedMessages), (acc, m) => {
      val node = m.destinatary
      val state = acc._1.get(node)
      val result = match m.message {
        | ProposalMessage(p) => handleProposal(p, state, allProposals)
        | VoteMessage(v) => handleVote(v, state, allProposals)
      }

      // Accumulate the result
      (
        acc._1.set(node, result._1),
        acc._2.union(result._2)
      )
    })

    all {
      protocolState' = accumulatedResult._1,
      messages' = accumulatedResult._2,
    }
  }

  /// A witness that is violated when there are no pending messages in the
  /// system, meaning that the system is not making progress and is stuck in a
  /// deadlock. This check is specific to our modelling of the protocol, and it
  /// relies on the fact that no timeouts/transmission mechanism was included in
  /// the system. This property doesn't fully cover the liveness property, as it
  /// doesn't take into account the possibility of a livelock.
  val deadlock = messages != Set()
  /* After checking this invariant, we discovered an issue with highQC field
  that is used to check the validity of extended certificates (a check on 3
  consecutive views with proposal.view - 1 = proposal.cert.view and
  proposal.cert.view - 1 = state.highQC). The problem here is that upon reaching
  the threshold for votes for the quorum proposal that precedes the extended
  proposal, the leader will form a quorum certificate and store it as highQC
  (function updateCerts is called in the main loop). This will cause the leader
  to reject it’s own proposal because the 3 consecutive views rule does not hold
  anymore (given that highQC was updated when forming the QC). As a consequence,
  a leader will not validate it’s own extended proposal and this creates a
  deadlock. This problem was not observed in the code. */

  /// If a node transitions to the next epoch (ie extended Quorum cert was
  /// formed) while other nodes are still in the current epoch, the nodes in the
  /// current epoch should have received the votes for extended QC. Apply this
  /// only on nodes that are part of e / e+1
  val transition = not(
    // some nodes are already in the next epoch
    protocolState.values().exists(s =>
      s.highQC != None and s.highQC.unwrap().block == K and s.highQC.unwrap().cType == Extended
    )
    and
    // the nodes in the current epoch have not received the votes for extended QC
    val nodes2 = protocolState.keys().filter(n => n.isInEpoch(2))
    val states2 = nodes2.map(n => protocolState.get(n))
    states2.exists(s => and {
      s.highQC != None,
      s.highQC.unwrap().block == K,
      s.highQC.unwrap().cType == Quorum,
      messages.filter(m => m.destinatary == s.node).getVotes()
        .filter(v => v.block == K and v.vType == Extended).size() == 0,
      // some nodes might receive the proposal with the QC from the leader before receiving the votes
      messages.filter(m => m.destinatary == s.node).getProposals()
        .filter(p => p.certificate.block == K and p.certificate.cType == Extended).size() == 0,
    })
  )
  /* After checking this invariant, we found that step 6 of the specs text
  explicitly requires nodes to send V_{v+2}ˆextended votes to all nodes in epoch
  e+1. However, the pseudocode implementation only reflects votes being
  transmitted to the leader, as it can be seen in the sendVote(vote) function.
  */

  /// A witness to generate a run where a transition into epoch 2 occured. It
  /// can be used to let the simulator generate an optimal scenario (as
  /// described in the English spec) using the stepWithoutTimeout action
  val optimalRun = not(protocolState.values().exists(s =>
    s.decidedQC != None and s.decidedQC.unwrap().block == K + 1)
  )

  /// A witness that allows us to let the simulator find runs where a timeout
  /// occurs in the epoch change using the standard step action. As the optimal
  /// runs needs 3 proposals, we look for a state with 4 proposals.
  val timeoutEpochRun = not(
    // we moved to the next epoch At least one node has a decided QC for the
    // first block of the next epoch
    protocolState.values().exists(s => s.decidedQC != None and s.decidedQC.unwrap().block == K + 1)
    and
    // block K was proposed more than 3 times, this comes from the fact that
    // view change needs to restart if interrupted by a view sync, resulting in
    // the block of height K being reproposed to build the 3 chain extended cert
    protocolState.values().exists(s => s.proposalArchive.filter(p => p.block == K).size() > 3)
    and
    // for all other blocks (1.to(K-1)) the block was proposed only once on all
    // nodes to avoid viewSyncs before the epoch change this can be eliminated
    // because the simulations tend to find a case that fits this naturally
    1.to(K-1).forall(b => {
      protocolState.values().forall(s => {
        val props = s.proposalArchive.filter(p => p.block == b)
        not(props.size() > 1)
      })
    })
  )
}

module hotshotTimeout {
  // V is a list of lists, where each inner list represents the validators for a specific epoch.
  // The first 2 views should be led by the node 1 to be compatible with our current initialization.
  // Look at the VALIDATOR CONSTANTS in the HotShotEpochReconfig module for more details.
  // NB: Every set has exactly N validators at most F of these N are faulty.
  pure val V = List(
    List(1, 1, 2, 3, 4, 1, 2, 3, 4),
    List(2, 6, 7, 1),
    List(1, 2, 4, 5),
    List(1, 5, 6, 8),
    List(2, 3, 4, 5)
  )

  import HotShotEpochReconfig(
    N = 4,
    F = 1,
    Q = 3,
    K = 5,
    MAX_NODES = 8,
    FAULTY = Set(),
    VALIDATORS = V
  ).*
}
