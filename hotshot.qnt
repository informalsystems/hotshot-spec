// -*- mode: Bluespec; -*-
module HotShotEpochReconfig {
    import types.* from "./types"

    import communication.* from "./communication"

    import basicSpells.* from "spells/basicSpells"

    //// **Constants** (system parameters)
    const N: int                      // total number of nodes (participants in consensus)
    const F: int                      // fault tolerance threshold (max number of Byzantine faults)
    const Q: int         /// quorum size (2F+1 signatures needed for decisions)
    const K: int         // duration of an epoch
    const TIMEOUT_DELAY: int          // maximum waiting time (in protocol steps) before triggering a timeout
    const MAX_NODES: int              // size of the universe of node IDs (>= N, to allow new nodes joining)
    const Faulty: Set[Node]

    //  Revise, this is only for protoyping
    pure val allNodes = 1.to(MAX_NODES)
    pure val stakingTables: List[StakingTable]=List(
    Set(1, 2, 4, 5),
    Set(1, 2, 6, 7),
    Set(1, 2, 4, 5),
    Set(1, 2, 3, 4),
    Set(1, 2, 4, 5),
    )
    pure val Leaders = Map(
        1 -> List(1, 1, 2, 2),
        2 -> List(1, 3, 6, 7),
        3 -> List(1, 2, 4, 5),
        4 -> List(1, 2, 3, 4),
        5 -> List(1, 2, 4, 5),
        6 -> List(1, 2, 4, 5),
        7 -> List(1, 2, 4, 5),
        8 -> List(1, 2, 4, 5),
    )

    val correct: Set[Node] = allNodes.exclude(Faulty)
    
    val allFaultyVotes : Set[Vote] = Set()
    val allFaultyProposals : Set[Proposal] = Set()

    var protocolState: ProtocolState

    //Maybe use this to store all the proposals seen
    var propAvailabilityLayer: Set[Proposal]
    
    
    //TODO: @Gabriela, is there a function for this in quint?
    pure def listContains(l: List[Block], block: Block): bool = {
        l.foldl(false, (acc, b) => acc or (b == block))
    }

    // Check if a node is part of the staking table for a given epoch
    // TODO add staking table to arguments
    pure def isInEpoch(node: Node, epoch: int): bool = {
        if (epoch <= 0 or epoch > length(stakingTables)) false
        else stakingTables[epoch-1].contains(node)
    }
    
    // Return the leader for a given view and epoch
    pure def leader(view: int, epoch: int): int = {
        //Leaders.get(epoch)[(view-1) % length(Leaders.get(epoch))]
        if (view == 3) 2
        else if (view == 4) 2
        else if (view == 7) 2
        else 1
        //1
    }

    
    // Return the epochs for which a node is active (only the current epoch or the current and next epoch)
    pure def getEpochs(node: Node, block: Block): Set[int] = {
        val isLastBlock = (block % K == 0)
        val epoch = if (isLastBlock) block / K else block / K + 1
        
        if (isLastBlock){
            if (isInEpoch(node, epoch) and isInEpoch(node, epoch+1)) Set(epoch,epoch+1)
            else if (isInEpoch(node, epoch)) Set(epoch)
            else if (isInEpoch(node, epoch+1)) Set(epoch+1)
            else Set()
        } else {
            if (isInEpoch(node, epoch)) Set(epoch)
            else Set()
        }
    }

    // Check if a node is the leader for a given view and block
    pure def isLeader(node: Node, view: int, block: int): bool = {
        val epoch = if (block % K == 0) block / K else block / K + 1
        node == leader(view, epoch)
    }

    pure def isSignatureValid(block: Block): bool = {
        true
    }

    // Check if a received vote is valid for a given node
    pure def isVoteValid(vote: Vote, node: Node, state: LocalState): bool = {
        val isLastBlock = (vote.block % K == 0)
        val epoch = if (isLastBlock) vote.block / K else vote.block / K + 1
        val validSignature = isSignatureValid(0)

        if (vote.view < state.view) false //Old vote
        else if (isLastBlock){ //Last block of the epoch
            if (vote.which != Extended and not(isLeader(node, vote.view+1, vote.block))) false // Quorum votes are sent only to leaders(Only extended are broadcasted)
            else if ((not (isInEpoch(node, epoch))) and (not (isInEpoch(node, epoch+1)))) false // If the not is not part of the epoch reconfig the vote is invalid
            else validSignature
        }
        else {
            if (not(isLeader(node, vote.view+1, vote.block))) false  
            else if (not (isInEpoch(node, epoch))) false
            else validSignature //TODO: The specs don't check if the vote here is for an extended proposal or not.
        }
    }


    pure def extends(a: Block, b: Block): bool = {
      a > b
    }

    // Return a proposal record
    pure def proposal(node: Node, block: Block, view: int, which: ProposalType, cert: Certificate): Proposal = {
        {sender: node, which: which, view: view, block: block, certificate: cert}
    }

    // Return a vote record
    pure def vote(node: Node, block: Block, view: int, which: VoteType): Vote = {
        {sender: node, which: which, view: view, block: block}
    }

    // Return a certificate record for a given block, 
    // includes optional extra signers for the next epoch if the block is the last of the current epoch
    pure def certificate(node: Node, which: CertificateType, view: int, block: Block, state: LocalState): Certificate = {
        val lastBlock = (block % K == 0)
        val epoch = if (lastBlock) block / K  else block / K + 1

        val signers = state.votesMap.getOrElse((which, block, view, epoch), Set())
        val basicCert = {which: which, signers: signers, nextEpochSigners: Set(),view: view, block: block}

        if (lastBlock){
            val nextSigners = state.votesMap.getOrElse((which, block, view, epoch + 1), Set())
            {...basicCert, nextEpochSigners: nextSigners}
        } else {
            basicCert
        }
    }


    // Form a proposal based on the certificate.
    pure def formProposal(node: Node, cert: Certificate, state: LocalState): Proposal = {
        
        if (cert.block % K == 0) { // Last block of the epoch

            if (cert.which == Extended) { // Extended proposal confirmed, propose the first block of the next epoch
                val newBlock = cert.block + 1
               proposal(node, newBlock, state.view, Quorum, cert)
            }

            else { // Quorum proposal confirmed, propose the same block until the epoch reconfiguration is done
                val newBlock = cert.block

                val newPropType =  // Determine the type of the proposal based on the highQC and lockedQC, is the 3 chain condition met?
                    if (state.highQC != None and state.lockedQC != None) {

                        val highQC = state.highQC.unwrap() 
                        val lockedQC = state.lockedQC.unwrap()

                        if (and {highQC.block == lockedQC.block, 
                                state.view - 1 == highQC.view, 
                                highQC.view - 1 == lockedQC.view}) Extended
                        else Quorum
                    
                    } else Quorum // If the QCs are not set, the extended proposal cannot be formed
        

                val newView = state.view
                proposal(node, newBlock, newView, newPropType, cert)
            }
        }
        
        else { // Not the last block of the epoch, propose the next block
            val newBlock = cert.block + 1
            proposal(node, newBlock, state.view, Quorum, cert)
        }
    }

    // Check if the proposal respects the safety and liveness properties
    pure def isProposalSafe(proposal: Proposal, state:LocalState): bool = {
        val lockedQC = state.lockedQC
        val block = proposal.block

        match(lockedQC){
            |None => true // No locked QC, the proposal is safe by default (TODO: Is this correct?)
            |Some(qc) => {
                or {
                    extends(block, qc.block), //safety
                    proposal.certificate.view > qc.view //liveness
                }
            }
        }
    }

    // Check if the certificate included in the proposal is valid
    pure def isCertValid(proposal: Proposal, state: LocalState): bool =
        val cert = proposal.certificate
        val block = proposal.block
        val epoch = if (block % K == 0) block / K else block / K + 1
        val isFirstBlock = (block % K == 1)
        val isLastBlock = (block % K == 0)
        
        if (isLastBlock){   // Last block of the epoch
            if (cert.which == Extended) false
            // Check if the proposal with the repeated block (ie part of epoch change) has enough signatures for the current and next epoch
            else if (block == cert.block) and{ size(cert.signers.filter(s => isInEpoch(s,epoch))) >= Q , size(cert.nextEpochSigners.filter(s => isInEpoch(s,epoch+1))) >= Q} 
            else and {isProposalSafe(proposal,state) , size(cert.signers.filter(s => isInEpoch(s,epoch))) >= Q}
        }

        else if (isFirstBlock and block !=1 ){ // First block of the epoch and not the genesis block
            if (cert.which != Extended) false
            else if (not(isProposalSafe(proposal, state))) false
            else and {size(cert.signers) >= Q , (size(cert.nextEpochSigners) >= Q)}
        }

        else { // Not first or last block of the epoch
            if (cert.which == Extended) false
            else if (not(isProposalSafe(proposal, state))) false
            else if (not(size(cert.signers.filter(s => isInEpoch(s,epoch))) >= Q)) false
            else true
        } 

    // Check if the extended proposal is valid
    pure def isExtendedProposalValid(proposal: Proposal, state: LocalState): bool = and {
        state.highQC != None,
        val highQC = state.highQC.unwrap()
        and {
          proposal.block == proposal.certificate.block,
          proposal.block == highQC.block,
          proposal.view - 1 == proposal.certificate.view,
          proposal.certificate.view - 1 == highQC.view
        }
    }

    // Check if the proposal is valid
    pure def isProposalValid(state: LocalState, proposal: Proposal): bool = {
        if (proposal.view < state.view) false
        else if (not(isSignatureValid(0))) false //Dummy signature check
        else if (not(isLeader(proposal.sender, proposal.view, proposal.block))) false
        else if ((proposal.which == Extended)) true//and (not(isExtendedProposalValid(proposal, state)))) false
        else if (not (isCertValid(proposal, state))) false
        else true
    }


    pure def fetchProposal(cert:Certificate, propDA: Set[Proposal]): Option[Proposal] = {
        //return the proposal that has the certificate
        propDA.find(prop => ( prop.block == cert.block and prop.view == cert.view))
    }

    // To be removed
    pure def certOrNeg(cert: Option[Certificate]): Certificate = {
        match(cert){
            |None => {which: Quorum, signers: Set(), nextEpochSigners: Set(),view: -1, block: -1}
            |Some(c) => c
        }
    }

    pure def updateCerts(node: Node, oldState: LocalState, cert: Certificate, allProps: Set[Proposal]): LocalState = {
      val highQC = cert
      val state = { ...oldState, highQC: Some(highQC)}
      val lockedQC = certOrNeg(state.lockedQC) //TODO: This is a hack, did this to avoid  having many nested match statements 
      val decidedQC = certOrNeg(state.decidedQC) //TODO: same as above

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
                    val updateLockedQC =  and {highQC.view - 1 == justifyHighQC.view, justifyHighQC.view > lockedQC.view}
                    val updateDecidedQC = and {justifyHighQC.view - 1 == justify2HighQC.view, justify2HighQC.view > decidedQC.view}

                    if (updateLockedQC and updateDecidedQC){
                        // This is helpful for debugging:

                        // the last block of the epoch is commited by the nodes of epoch+1
                        val epoch = justify2HighQC.block / K + 1
                        val nodeInEpoch = isInEpoch(node, epoch)
                        
                        val newChain = if ((not (listContains(state.chain, justify2HighQC.block))) and nodeInEpoch) state.chain.append(justify2HighQC.block) else state.chain    
                        { ...state, highQC: Some(highQC), lockedQC: Some(justifyHighQC), decidedQC: Some(justify2HighQC), chain: newChain, decidedQCArchive: state.decidedQCArchive.append(justify2HighQC)}
                    } else if (updateLockedQC){
                        { ...state, highQC: Some(highQC), lockedQC: Some(justifyHighQC)}
                    } else if (updateDecidedQC){  
                        { ...state, highQC: Some(highQC), decidedQC: Some(justify2HighQC),chain: state.chain.append(justify2HighQC.block)}
                    } else {
                        { ...state, highQC: Some(highQC)} 
                } 
            }
          
          }
        }
      } 
    }


    // Update the node's Votes Map with the new vote
    pure def accumulateSignatures(vote: Vote, node: Node, state: LocalState): LocalState = { 
        val epochs = getEpochs(node, vote.block)

        // For each relevant epoch, add the voter to the votes map
        val newVotes = epochs.fold(state.votesMap, (newVotesMap, e) => {
            val key = (vote.which, vote.block, vote.view, e)
            newVotesMap.setByWithDefault(key, voters => voters.union(Set(vote.sender)).filter(s => isInEpoch(s,e)), Set())
        })
        { ...state, votesMap: newVotes }
    }

    // Check if a quorum of votes has been reached for a proposal based on the accumulated votes
    pure def threshholdReached(vote: Vote, state: LocalState): bool = {
        val epochs = if (vote.block % K == 0) Set(vote.block / K, vote.block / K + 1) else Set(vote.block / K + 1)
        
        // For each relevant epoch, check if we have enough votes
        epochs.forall(e => {
                val key = (vote.which, vote.block, vote.view, e)
                val voters = state.votesMap.getOrElse(key, Set())
                voters.size() >= Q
            })
    }

    // Send a proposal to the leader (either the current leader or the next epoch leader)
    pure def sendVoteToLeader(state: ProtocolState, v: Node, vote: Vote): ProtocolState = {
        pure val epoch = if (vote.block % K == 0) vote.block / K else vote.block / K + 1
        pure val localState = state.get(v)

        pure val leaderToSend = if (vote.which == Extended) {
          leader(localState.view + 1, epoch + 1)
        } else {
          leader(localState.view + 1, epoch)
        }
        sendVote(state, leaderToSend, vote)
    }

    // Deliver a vote from the network buffer to the node
    action deliverVote(n: Node, vote: Vote): bool ={
        //exclude vote from buffer and add to votes
        val newVotesBuffer = protocolState.get(n).votesBuffer.exclude(Set(vote))
        val newVotes = protocolState.get(n).votes.union(Set(vote))
        all {
            protocolState.get(n).votesBuffer.union(allFaultyVotes).contains(vote),
            protocolState' = protocolState.setBy(n, state => { ...state, votesBuffer: newVotesBuffer, votes: newVotes }),
            propAvailabilityLayer' = propAvailabilityLayer //TODO: This is a hack, need to fix
        }
    }

    // Deliver a proposal from the network buffer to the node
    action deliverProposal(n: Node, prop: Proposal): bool ={
        //exclude proposal from buffer and add to proposals
        val newPropsBuffer = protocolState.get(n).propsBuffer.exclude(Set(prop))
        val newProps = protocolState.get(n).proposals.union(Set(prop))
        all {
            protocolState.get(n).propsBuffer.union(allFaultyProposals).contains(prop),
            protocolState' = protocolState.setBy(n, state => { ...state, propsBuffer: newPropsBuffer, proposals: newProps }),
            propAvailabilityLayer' = propAvailabilityLayer //TODO: This is a hack, need to fix
        }
    }

    //Non-deterministically chooses a message type (proposal, vote) and delivers it.
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


    pure def handleVote(vote: Vote, pState: ProtocolState, node: Node, allProps: Set[Proposal]): ProtocolState = {
        
        val oldState = pState.get(node)
        val state = { ...oldState, votes: oldState.votes.exclude(Set(vote)), voteArchive: oldState.voteArchive.union(Set(vote))}
        val epoch = if (vote.block % K == 0) vote.block / K else vote.block / K + 1
        val NODES = pState.keys()

        
        if (isVoteValid(vote, node, state)){
            val stateWithSig = accumulateSignatures(vote, node, state)

            if (threshholdReached(vote, stateWithSig)){
                // Form a certificate
                val cert = certificate(node, vote.which, vote.view, vote.block, stateWithSig)
                val stateWithCerts = updateCerts(node ,stateWithSig, cert, allProps)
                val newView = cert.view + 1
                val newState = { ...stateWithCerts, view: newView }
                if (isLeader(node,vote.view + 1, epoch)){
                // Form a proposal
                    val newProp = formProposal(node, cert, newState)
                    val newPropEpoch = if (newProp.block % K == 0) newProp.block / K else newProp.block / K + 1
                    // Update certificates based on the proposal's certificate
                    val receivers =
                        if (newProp.block % K == 0){
                            NODES.filter(n => isInEpoch(n, newPropEpoch) or isInEpoch(n, newPropEpoch + 1))
                        } else {
                            NODES.filter(n => isInEpoch(n, newPropEpoch))
                        }
                    multicastProposal(pState.setBy(node, state => newState), receivers, newProp)
                } else {
                    pState.setBy(node, state => newState)
                }
            } else {
                // Do nothing
                pState.setBy(node, state => stateWithSig)
            }
        } else {
            // Do nothing
            pState.setBy(node, s => state)
        }
    }

    pure def handleProposal(prop: Proposal, pState: ProtocolState, node: Node, allProps: Set[Proposal]): ProtocolState = {
        val oldState = pState.get(node)
        val state = { ...oldState, proposals: oldState.proposals.exclude(Set(prop)), proposalArchive: oldState.proposalArchive.union(Set(prop))}
        
        if (isProposalValid(state, prop)){
            val stateWithcerts = updateCerts(node,state, prop.certificate, allProps)
            val newView = prop.view
            val newState = { ...stateWithcerts, view: newView}
            val newVote = vote(node, prop.block, prop.view, prop.which)
            val newPstate = pState.setBy(node, state => newState)
            sendVoteToLeader(newPstate, node, newVote) //update this by sending to the nodes in epoch e+1 when needed
        } else {
            pState.setBy(node, s => state)
        }
    }

    pure def nodeHandler(node: Node, pState: ProtocolState, allProps: Set[Proposal]) : ProtocolState = {
        val state = pState.get(node)
        val currentView = state.view
        val currentVotes = state.votes
        val currentProps = state.proposals
        
        if (currentVotes.size() > 0){
            currentVotes.fold(pState, (updatedState, vote) => {
                handleVote(vote, pState, node, allProps)})
            
        }
        else if (currentProps.size() > 0){
            currentProps.fold(pState, (updatedState, prop) => {
                handleProposal(prop, pState, node, allProps)})
        }
        else {
            pState
        }
    }

    // accumulate all proposals from the whole history 
    pure def stateToAllProposals(pState: ProtocolState, allProps: Set[Proposal]): Set[Proposal] = {
        pState.values().fold(allProps, (props, state) => {
            props.union(state.proposals).union(state.propsBuffer)
        })
    }
    

    val genesisCert = {
        which: Quorum, 
        signers: Set(1, 2, 4), 
        nextEpochSigners: Set(),
        view: 0, 
        block: 0
    }

    val genesisProp = {
        sender: 1, 
        which: Quorum, 
        view: 1, 
        block: 1, 
        certificate: genesisCert
    }

    action init = all {
      protocolState' = 1.to(MAX_NODES).mapBy(node => {
        epoch: 1,
        view: 0,
        highQC: None,
        lockedQC: None,
        decidedQC: None,
        chain: List(),
        decidedQCArchive: List(),
        proposals: Set(),
        votes: Set(),
        proposalArchive: Set(),
        voteArchive: Set(),
        votesMap: Map(),
        votesBuffer: Set(),
        propsBuffer: Set(genesisProp),
      }),
       propAvailabilityLayer' = Set(genesisProp)
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
                propAvailabilityLayer' = stateToAllProposals(protocolState, propAvailabilityLayer),
                protocolState' = nodeHandler(v, protocolState, propAvailabilityLayer)
            }
        }
    }



    // quint run hotshot.qnt --invariant=witness to try to find an interesting couterexample
    // where this property doesn't hold
    val witness = true
}

module hotshot {
  // Some arbitrary numbers, just to enable simulation
  import HotShotEpochReconfig(N = 4, F = 1, Q = 3, K = 5, TIMEOUT_DELAY = 4, MAX_NODES = 8, Faulty = Set()).*
}
