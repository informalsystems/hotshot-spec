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

    //Maybe use this to store all the proposals seen
    var propAvailabilityLayer: Set[Proposal]
    
    
    //
    // Verification & validity functions
    //

    pure def isInEpoch(node: Node, epoch: int): bool = {
        // epochs start at 0
        // Check if the node is part of the staking table for the given epoch
        // If stakingTables list is empty or epoch is out of bounds, default to true
        if (epoch < 0 or epoch >= length(stakingTables)) false
        else stakingTables[epoch].contains(node)
    }
    
    pure def leader(view: int, epoch: int): int = {
        1
    }

    pure def isLeader(node: Node, view: int, block: int): bool = {
        val epoch = if (block % K == 0) block / K else block / K + 1
        node == leader(view, epoch)
    }

    pure def isSignatureValid(dummy: int): bool = {
        true
    }


    pure def isVoteValid(vote: Vote, node: Node, state: LocalState): bool = {
        val isLastBlock = (vote.block % K == 0)
        val epoch = if (isLastBlock) vote.block / K else vote.block / K + 1
        val validSignature = isSignatureValid(0)

        if (vote.view < state.view) false //Old vote
        else if (isLastBlock){
            if (vote.which != Extended and not(isLeader(node, vote.view+1, vote.block))) false
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
      // In a blockchain, block a extends block b if a has a higher height than b
      // and a is built on top of b (directly or indirectly)
      // Since we're only storing block height currently, we check if a > b
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
        if (cert.which == Extended) false
        else if (block == cert.block) false //TODO correctlySigned(cert, epoch) and correctlySigned(cert, epoch + 1) cert is signed by quorum in e and e+1
        else isProposalSafe(proposal, node, state) // TODO and correctlySigned(cert, epoch)
        }

        else if (isFirstBlock){ //First block of the epoch
        if (cert.which != Extended) false
        else if (not(isProposalSafe(proposal, node, state))) false
        // else if not correctly signed by epoch and epoch - 1 false
        else true
        }

        else { // Not first or last block of the epoch
        if (cert.which == Extended) false
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

    pure def isProposalValid(state: LocalState, proposal: Proposal): bool = {
        if (proposal.view < state.view) false
        else if (not(isSignatureValid(0))) false //TODO: args need to be changed
        else if (not(isLeader(proposal.sender, proposal.view, proposal.block))) false
        else if ((proposal.which == Extended) and (not(isExtendedProposalValid(proposal, proposal.sender, state))))
        false
        else if (not (isJustifyCertValid(proposal, proposal.sender, state))) false
        else true
    }

    pure def fetchProposal(cert:Certificate, propDA: Set[Proposal]): Option[Proposal] = {
        //return the proposal that has the certificate
        propDA.find(prop => prop.certificate == cert)
    }

    // To be removed
    pure def certOrNeg(cert: Option[Certificate]): Certificate = {
        match(cert){
            |None => {which: Quorum, signers: Set(), view: -1, block: -1}
            |Some(c) => c
        }
    }

    pure def updateCerts(state: LocalState, cert: Certificate, allProps: Set[Proposal]): LocalState = {
      val highQC = cert
      val lockedQC = certOrNeg(state.lockedQC) //TODO: This is a hack, need to fix
      val decidedQC = certOrNeg(state.decidedQC) //TODO: This is a hack, need to fix
      val justifyHighP = fetchProposal(highQC, allProps)
      match(justifyHighP){
        |None => state
        |Some(p) => {
            val justifyHighQC = p.certificate
            val justify2HighP = fetchProposal(justifyHighQC, allProps)
            match(justify2HighP){
                |None => state
                |Some(p2) => {
                    val justify2HighQC = p2.certificate
                    val updateLockedQC = and {highQC.view - 1 == justifyHighQC.view, justifyHighQC.view > lockedQC.view}
                    val updateDecidedQC = and {justifyHighQC.view - 1 == justify2HighQC.view, justify2HighQC.view > decidedQC.view}

                    if (updateLockedQC and updateDecidedQC){
                        { ...state, highQC: Some(highQC), lockedQC: Some(justifyHighQC), decidedQC: Some(justify2HighQC)}
                    } else if (updateLockedQC){
                        { ...state, highQC: Some(highQC), lockedQC: Some(justifyHighQC)}
                    } else if (updateDecidedQC){ //this can be ommited maybe ?
                        { ...state, highQC: Some(highQC), decidedQC: Some(justify2HighQC) }
                    } else {
                        { ...state, highQC: Some(highQC)} 
                } 
            }
          
          }
        }
      } 
    }

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

    pure def accumulateSignatures(vote: Vote, node: Node, state: LocalState): LocalState = { 
        val epochs = getEpochs(node, vote.block)
        val newVotes = epochs.fold(state.votesMap, (newVotesMap, e) => {
            val key = (vote.which, vote.block, vote.view, e)
            newVotesMap.setByWithDefault(key, voters => voters.union(Set(node)), Set())
        })
        { ...state, votesMap: newVotes }
    }

    pure def threshholdReached(vote: Vote, state: LocalState): bool = {
        // Check if we have enough votes (Q signatures) for this vote
        val epochs = getEpochs(vote.sender, vote.block)
        
        // For each relevant epoch, check if we have enough votes
        epochs.exists(e => {
            val key = (vote.which, vote.block, vote.view, e)
            val voters = state.votesMap.getOrElse(key, Set())
            voters.size() >= Q
        })
    }

    pure def sendVoteToLeader(state: ProtocolState, v: Node, vote: Vote): ProtocolState = {
        pure val epoch = if (vote.block % K == 0) {
            vote.block / K
        } else {
            vote.block / K + 1
        }

        pure val localState = state.get(v)
        pure val leaderToSend = if (vote.which == Extended) {
          leader(localState.view + 1, localState.epoch + 1)
        } else {
          leader(localState.view + 1, localState.epoch)
        }
        sendVote(state, leaderToSend, vote)
    }

    action deliverVote(n: Node, vote: Vote): bool ={
        //exclude vote from buffer and add to votes
        val newVotesBuffer = protocolState.get(n).votesBuffer.exclude(Set(vote))
        val newVotes = protocolState.get(n).votes.union(Set(vote))
        all {
            protocolState.get(n).votesBuffer.union(allFaultyVotes).contains(vote),
            protocolState' = protocolState.setBy(n, state => { ...state, votesBuffer: newVotesBuffer, votes: newVotes })
        }
    }

    action deliverProposal(n: Node, prop: Proposal): bool ={
        //exclude proposal from buffer and add to proposals
        val newPropsBuffer = protocolState.get(n).propsBuffer.exclude(Set(prop))
        val newProps = protocolState.get(n).proposals.union(Set(prop))
        all {
            protocolState.get(n).propsBuffer.union(allFaultyProposals).contains(prop),
            protocolState' = protocolState.setBy(n, state => { ...state, propsBuffer: newPropsBuffer, proposals: newProps })
        }
    }

    //Non-deterministically chooses a message type (proposal, vote) and receives it.
    action deliverMessage(v: Node): bool = {
        val state = protocolState.get(v)
        any {
          val props = state.propsBuffer.union(allFaultyProposals)
          all {
              props.size() > 0,
              nondet prop = oneOf(props)
              deliverProposal(v, prop),
          },
          val votes = state.votesBuffer.union(allFaultyVotes)
          all {
              votes.size() > 0,
              nondet vote = oneOf(votes)
              deliverVote(v, vote),
          }
        }
    }

    
    pure def nodeHandler(node: Node, state: LocalState, allProps: Set[Proposal]) : LocalState = {
        val currentView = state.view
        val currentVotes = state.votes
        val currentProps = state.proposals
        
        if (q::debug("Processing votes", currentVotes.size() > 0)){
            // Handle votes and update state
            // If this node is a leader for the current view, it should collect votes
            // and form certificates when enough votes are received
            
            // Process each vote
            
            currentVotes.fold(state, (updatedState, vote) => {
                // Check if the vote is valid
                if (isVoteValid(vote, node, updatedState)) {
                    // Accumulate the vote
                    val stateWithVote = accumulateSignatures(vote, vote.sender, updatedState)
                    
                    // Check if we have enough votes to form a certificate
                    if (threshholdReached(vote, stateWithVote)) {
                        // Create a new certificate
                        val key = (vote.which, vote.block, vote.view, updatedState.epoch)
                        val signers = stateWithVote.votesMap.getOrElse(key, Set())
                        val newCert = { which: vote.which, signers: signers, view: vote.view, block: vote.block }
                        
                        // Update certificates
                        updateCerts(stateWithVote, newCert, allProps)
                    } else {
                        stateWithVote
                    }
                } else {
                    updatedState
                }
            })
        }
        else if (q::debug("Processing Props", currentProps.size() > 0)){
            // Handle proposals and update state
            // Process each proposal
            currentProps.fold(state, (updatedState, prop) => {
                // Check if the proposal is valid
                if (isProposalValid(updatedState, prop)) {
                    // Update certificates based on the proposal's certificate
                    val stateWithCerts = updateCerts(updatedState, prop.certificate, allProps)
                    
                    // Update view to match the proposal's view
                    { ...stateWithCerts, view: prop.view }
                } else {
                    updatedState
                }
            })
        }
        else {
            state
        }
    }
    

    action init = {
      protocolState' = 1.to(MAX_NODES).mapBy(node => {
        epoch: 0,
        view: 0,
        highQC: None,
        lockedQC: None,
        decidedQC: None,
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
            // Receive and process a message
            deliverMessage(v),
            all {
                val nodeState = protocolState.get(v)
                val updatedState = nodeHandler(v, nodeState, propAvailabilityLayer)
                protocolState' = protocolState.put(v, updatedState)
            }
        }
    }

    // quint run hotshot.qnt --invariant=witness to try to find an interesting couterexample
    // where this property doesn't hold
    // Doesn't find any yet because we aren't generating any valid proposals
    val witness = protocolState.values().forall(state => state.highQC == None)
}

module hotshot {
  // Some arbitrary numbers, just to enable simulation
  import HotShotEpochReconfig(N = 4, F = 1, Q = 3, K = 2, TIMEOUT_DELAY = 4, MAX_NODES = 7, Faulty = Set(3)).*
}
