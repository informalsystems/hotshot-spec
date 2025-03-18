module HotShotEpochReconfig {
    import types.* from "./types"

    import communication.* from "./communication"

    import basicSpells.* from "spells/basicSpells"

    //// **Constants** (system parameters)
    const N: int                      // total number of nodes (participants in consensus)
    const F: int                      // fault tolerance threshold (max number of Byzantine faults)
    const Q: int         /// quorum size (2F+1 signatures needed for decisions)&#8203;:contentReference[oaicite:0]{index=0}
    const K: int         // duration of an epoch
    const TIMEOUT_DELAY: int          // maximum waiting time (in protocol steps) before triggering a timeout
    const MAX_NODES: int              // size of the universe of node IDs (>= N, to allow new nodes joining)
    const Faulty: Set[Node]

    //  Revise, this is only for protoyping
    pure val allNodes = 1.to(MAX_NODES)
    pure val stakingTables: List[StakingTable]= List()
    val correct: Set[Node] = allNodes.exclude(Faulty)
    
    val allFaultyVotes : Set[Vote] = Set()
    val allFaultyProposals : Set[Proposal] = Set()

    var protocolState: ProtocolState
    
    
    //// **Local pure functions** (helpers for logic, no state modification)

    //
    // Verification & validity functions
    //

    pure def isInEpoch(node: Node, epoch: int): bool = //TODO: implement epoch check
        true
    
    //TODO: I think it is possible to get the leader only from the view number(look at paper fig 3)
    pure def leader(view: int, epoch: int): int = //TODO: implement leader election
        0

    pure def isLeader(node: Node, view: int, block: int): bool =
        val epoch = if (block % K == 0) block / K else block / K + 1
        node == leader(view, epoch)

    pure def isSignatureValid(dummy: int): bool = //TODO: implement signature verification
        true


    pure def isVoteValid(vote: Vote, node: Node, state: LocalState): bool = {
        val isLastBlock = (vote.block % K == 0)
        val epoch = if (isLastBlock) vote.block / K else vote.block / K + 1
        val validSignature = isSignatureValid(0)

        if (vote.view < state.view) false //Old vote
        else if (isLastBlock){
            if (vote.which != ExtendedV and not(isLeader(node, vote.view+1, vote.block))) false
            else if ((not (isInEpoch(node, epoch))) and (not (isInEpoch(node, epoch+1)))) false
            else validSignature
        }
        else {
            if (not(isLeader(node, vote.view+1, vote.block))) false
            else if (not (isInEpoch(node, epoch))) false
            else validSignature
        }
    }

    pure def extends(a: Block, b: Block): bool = {
      // TODO: implement extends logic
      a > b
    }

    pure def isProposalSafe(proposal: Proposal, node:Node, state:LocalState): bool = and {
      state.lockedQC != None,
      pure val lockedQC = state.lockedQC.unwrap()
      or {
        proposal.block.extends(lockedQC.block), // Safety Rule
        proposal.certificate.view > lockedQC.view, // Liveness Rule
      }
    }

    pure def isJustifyCertValid(proposal: Proposal, node: Node, state: LocalState): bool =
        val cert = proposal.certificate
        val block = proposal.block
        val epoch = if (block % K == 0) block / K else block / K + 1
        val isFirstBlock = (block % K == 1)
        val isLastBlock = (block % K == 0)

        if (isLastBlock){ //Last block of the epoch
        if (cert.which == ExtendedC) false
        else if (block == cert.block) false //TODO correctlySigned(cert, epoch) and correctlySigned(cert, epoch + 1) cert is signed by quorum in e and e+1
        else isProposalSafe(proposal, node, state) // TODO and correctlySigned(cert, epoch)
        }

        else if (isFirstBlock){ //First block of the epoch
        if (cert.which != ExtendedC) false
        else if (not(isProposalSafe(proposal, node, state))) false
        // else if not correctly signed by epoch and epoch - 1 false
        else true
        }

        else { // Not first or last block of the epoch
        if (cert.which == ExtendedC) false
        else if (not(isProposalSafe(proposal, node, state))) false //TODO correctlySigned(cert, epoch) and correctlySigned(cert, epoch + 1) cert is signed by quorum in e and e+1
        //else if not correctly signed by epoch false
        else true
        } 

    pure def isExtendedProposalValid(proposal: Proposal, node: Node, state: LocalState): bool = and {
        // TODO: implement extended proposal verification
        state.highQC != None,
        val hightQC = state.highQC.unwrap()
        and {
          // The proposed block must be the same as in the justify QC
          // and in the current high_qc
          proposal.block == proposal.certificate.block,
          proposal.block == hightQC.block,
          // The proposal, the justify qc and the high qc
          // need to me formed in three consecutive views
          proposal.view - 1 == proposal.certificate.view,
          proposal.certificate.view - 1 == hightQC.view
          // If this proposal is eventually accepted by this node
          // the justify qc will become a high qc and the high qc
          // will become a locked qc. The certificate formed based
          // on this proposal will become an eQC
        }
    }

    pure def isProposalValid(proposal: Proposal, node: Node, state: LocalState): bool ={
        if (proposal.view < state.view) false
        else if (not(isSignatureValid(0))) false //TODO: args need to be changed
        else if (not(isLeader(proposal.sender, proposal.view, proposal.block))) false
        else if ((proposal.which == ExtendedP) and (not(isExtendedProposalValid(proposal, proposal.sender, state)))) 
        false
        else if (not (isJustifyCertValid(proposal, proposal.sender, state))) false
        else true
    }

    //pure def updateCerts

    //utility function to get the epochs that a node is part of, used for vote accumulation
    pure def getEpochs(node: Node, block: Block): Set[int] = {
        val epochs = Set()
        val isLastBlock = (block % K == 0)
        val epoch = if (isLastBlock) block / K else block / K + 1
        if (isLastBlock){
            if (isInEpoch(node, epoch) and isInEpoch(node, epoch+1)) epochs.union(Set(epoch)).union(Set(epoch+1))
            else if (isInEpoch(node, epoch)) epochs.union(Set(epoch))
            else if (isInEpoch(node, epoch+1)) epochs.union(Set(epoch+1))
            else epochs
        } else {
            if (isInEpoch(node, epoch)) epochs.union(Set(epoch))
            else epochs
        }
    }

    //TODO: OR Accumulate votes
    pure def accumulateSignatures(vote: Vote, node: Node, state: LocalState): LocalState = { 
        val epochs = getEpochs(node, vote.block)
        val newVotes = epochs.fold(state.votesMap, (newVotesMap, e) => {
            val key = (vote.which, vote.block, vote.view, e)
            newVotesMap.setByWithDefault(key, voters => voters.union(Set(node)), Set())
        })
        { ...state, votesMap: newVotes }
    }

    pure def threshholdReached(vote: Vote): bool = {
        //TODO: Implement quorum check
        true
    }



    action receiveVote(n: Node, vote: Vote): bool ={
        //exclude vote from buffer and add to votes
        val newVotesBuffer = protocolState.get(n).votesBuffer.exclude(Set(vote))
        val newVotes = protocolState.get(n).votes.union(Set(vote))
        all {
            protocolState.get(n).votesBuffer.union(allFaultyVotes).contains(vote),
            protocolState' = protocolState.setBy(n, state => { ...state, votesBuffer: newVotesBuffer, votes: newVotes })
        }
    }

    action receiveProposal(n: Node, proposal: Proposal): bool = {
        //exclude proposal from buffer and add to proposals
        val newPropsBuffer = protocolState.get(n).propsBuffer.exclude(Set(proposal))
        val newProps = protocolState.get(n).proposals.union(Set(proposal))
        all {
            protocolState.get(n).propsBuffer.union(allFaultyProposals).contains(proposal),
            protocolState' = protocolState.setBy(n, state => { ...state, propsBuffer: newPropsBuffer, proposals: newProps })
        }
    }

    //Non-deterministically chooses a message type (proposal, vote) and receives it.
    action receiveMessage(v: Node): bool = any {
        val props = protocolState.get(v).propsBuffer.union(allFaultyProposals)
        all{
            props.size() > 0,
            nondet prop = oneOf(props)
            receiveProposal(v, prop),
        },
        val votes = protocolState.get(v).votesBuffer.union(allFaultyVotes)
        all {
            votes.size() > 0,
            nondet vote = oneOf(votes)
            receiveVote(v, vote),
        }
    }

    action newVote(v: Node): bool = {
      // TODO: This is arbitrary, we should generate proper votes here
      val nodeState = protocolState.get(v)
      nondet voteType = Set(QuorumV, ExtendedV, NoneV).oneOf()
      val vote = { sender: v, which: voteType, view: nodeState.view, block: K }
      protocolState' = protocolState.broadcastVote(vote)
    }

    action newProposal(v: Node): bool = {
      // TODO: This is arbitrary, we should generate proper proposals here
      val nodeState = protocolState.get(v)
      nondet propType = Set(QuorumP, ExtendedP, NoneP).oneOf()
      nondet certType = Set(QuorumC, ExtendedC, NoneC).oneOf()
      val cert = { which: certType, signers: Set(v), view: nodeState.view, block: K }
      val prop = { sender: v, which: propType, view: nodeState.view, block: K, certificate: cert }
      protocolState' = protocolState.broadcastProposal(prop)
    }

    
    pure def nodeHandler(node: Node, state: LocalState) : LocalState = {
        // TODO: Why the get on the protocolState didn't work?
        val currentView = state.view
        // TODO: @Gabriela, do we need to handle votes only in the view? I think it wont allow the 
        // node to make progress .
        // The asynchrony is handled anyway by the deliver action so we should be fine with this.
        val currentVotes = state.votes
        val currentProps = state.proposals
        
        if (currentVotes.size() > 0) {
            //Handle votes and update state
            // votes have different logic based on role of the node (leader or not)
            // if the node is a leader for the block included in the vote can be computed.
            state
        }
        else if (currentProps.size() > 0) {
            //Handle proposals and update state
            state
        }
        else {
            state
        }
    }
    
    /*
    Validators process proposals and votes asynchronously.
    Each validator executes the next step (nextAction()) asynchronously.
    The system updates state accordingly
    action valStep(v: Address) : bool = {
        val next_action = system.get(v).nextAction() 
        val node_state = next_action._1
        val driver_input = next_action._2
        val sys1 = system.put(v, node_state)
        val res = driver(sys1.get(v).es, driver_input)
        val driver_state = res.ds
        val consensus_output = res.out
        all {
            system' = sys1.put(v, { ...sys1.get(v), es: driver_state}),
            certBuffer' = sendCertificate(certBuffer, res.certificate),
            _hist' = { validator: v, input: driver_input, output: consensus_output }
        }
    }*/


    action init = {
      protocolState' = 1.to(MAX_NODES).mapBy(node => {
        epoch: 0,
        view: 0,
        highQC: None,
        lockedQC: None,
        proposals: Set(),
        votes: Set(),
        votesMap: Map(),
        votesBuffer: Set(),
        propsBuffer: Set(),
      })
    }
    
    /*
    Execution Loop
    The execution step (step) randomly picks a validator and either:
        Handles a received message 
        Delivers a pending message (deliver).
        ... Maybe separate handling messages from sending responses to have more atomic actions
    */
    action step = {
        nondet v = oneOf(correct)
        any {
            receiveMessage(v),
            newVote(v),
            newProposal(v),
            //something modeled after valsStep,
        }
    } // TODO
}

module hotshot {
  // Some arbitrary numbers, just to enable simulation
  import HotShotEpochReconfig(N = 4, F = 1, Q = 3, K = 2, TIMEOUT_DELAY = 4, MAX_NODES = 7, Faulty = Set(3)).*
}
