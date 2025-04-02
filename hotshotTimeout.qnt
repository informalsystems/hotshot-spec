// -*- mode: Bluespec; -*-
module HotShotEpochReconfig {
    import types.* from "./types"

    import communication.* from "./communication"

    import basicSpells.* from "spells/basicSpells"
    import rareSpells.* from "spells/rareSpells"

    //// **Constants** (system parameters)
    const N: int                      // total number of nodes (participants in consensus)
    const F: int                      // fault tolerance threshold (max number of Byzantine faults)
    const Q: int         /// quorum size (2F+1 signatures needed for decisions)
    const K: int         // duration of an epoch
    const MAX_NODES: int              // size of the universe of node IDs (>= N, to allow new nodes joining)
    const FAULTY: Set[Node]

    //  Revise, this is only for protoyping
    pure val allNodes = 1.to(MAX_NODES)
    pure val correct: Set[Node] = allNodes.exclude(FAULTY)

    pure val stakingTables: List[StakingTable]=List(
        Set(1, 2, 4, 5),
        Set(1, 2, 6, 7),
        Set(1, 2, 4, 5),
        Set(1, 5, 6, 8),
        Set(2, 3, 4, 5),
    )
        
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
        val epochIndex = (epoch - 1) % length(stakingTables)
        if (epoch <= 0) false
        else stakingTables[epochIndex].contains(node)
    }
    
    // Return the leader for a given view and epoch
    pure def leader(view: int, epoch: int): int = {
        val epochIndex = (epoch - 1) % length(stakingTables)
        val viewIndex = view % size(stakingTables[epochIndex])

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
        
        if (cert.block % K == 0 and cert.block > 0)  { // Last block of the epoch

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
        else if (((proposal.which == Extended)) and (not(isExtendedProposalValid(proposal, state)))) false
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

    pure def updateCerts(node: Node, oldState: LocalState, cert: Certificate, allProps: Set[Proposal]): LocalState = {
        val highQC = cert
        val state = { ...oldState, highQC: Some(highQC), highQCArchive: updateHighQCMap(highQC, oldState.highQCArchive) }
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

                            val newChain = commitedBlocks(justify2HighQC, decidedQC, state.highQCArchive)
                            // TODO: can we use allProps here?
                            //val traverse = state.acceptedProposals.filter(p => (p.certificate.block >= decidedQC.block) and (p.certificate.block <= justify2HighQC.block))
                            //val chainS = traverse.map(p => p.certificate.block)
                            // eliminate the duplicates by keeping the one with the highest view

                            //val newChain = if ((not (listContains(state.chain, justify2HighQC.block))) and nodeInEpoch) state.chain.append(justify2HighQC.block) else state.chain    
                            //val newChain = state.chain.append(chainS)
                            { ...state, highQC: Some(highQC), lockedQC: Some(justifyHighQC), decidedQC: Some(justify2HighQC)}//, chain: newChain, decidedQCArchive: state.decidedQCArchive.append(justify2HighQC)}
                        } else if (updateLockedQC){
                            { ...state, highQC: Some(highQC), lockedQC: Some(justifyHighQC)}
                        } else if (updateDecidedQC){  
                            val epoch = justify2HighQC.block / K + 1
                            val nodeInEpoch = isInEpoch(node, epoch)
                            
                            //val traverse = state.acceptedProposals.filter(p => (p.certificate.block >= decidedQC.block) and (p.certificate.block <= justify2HighQC.block))
                            //val chainS = traverse.map(p => p.certificate.block)
                            // eliminate the duplicates by keeping the one with the highest view
                            
                            //val newChain = state.chain.append(chainS)

                            //val newChain = if ((not (listContains(state.chain, justify2HighQC.block))) and nodeInEpoch) state.chain.append(justify2HighQC.block) else state.chain    
                            { ...state, highQC: Some(highQC), decidedQC: Some(justify2HighQC)}//, chain: newChain, decidedQCArchive: state.decidedQCArchive.append(justify2HighQC)}
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

    pure def handleVote(vote: Vote, pState: ProtocolState, node: Node, allProps: Set[Proposal]): ProtocolState = {
        val oldState = pState.get(node)
        val state = { ...oldState, votesBuffer: oldState.votesBuffer.exclude(Set(vote)), voteArchive: oldState.voteArchive.union(Set(vote))}
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
        val state = { ...oldState, propsBuffer: oldState.propsBuffer.exclude(Set(prop)), proposalArchive: oldState.proposalArchive.union(Set(prop))}
        
        if (isProposalValid(state, prop)){
            val stateWithcerts = updateCerts(node, state, prop.certificate, allProps)
            val newView = prop.view
            val newState = { ...stateWithcerts, view: newView}
            val newVote = vote(node, prop.block, prop.view, prop.which)
            val newPstate = pState.setBy(node, state => newState)
            sendVoteToLeader(newPstate, node, newVote) //update this by sending to the nodes in epoch e+1 when needed
        } else {
            pState.setBy(node, s => state)
        }
    }

    pure def stateToAllProposals(pState: ProtocolState, allProps: Set[Proposal]): Set[Proposal] = {
        pState.values().fold(allProps, (props, state) => {
            props.union(state.propsBuffer).union(state.proposalArchive)
        })
    }

    // Get the highest view number among all correct nodes
    pure def getHighestView(pState: ProtocolState): int = {
        correct.fold(0, (maxView, node) => {
            val nodeView = pState.get(node).view
            if (nodeView > maxView) nodeView else maxView
        })
    }

    // Update a node's state to a new view
    pure def updateToNewView(state: LocalState, newView: int): LocalState = {
        if (newView > state.view) {
            {...state, view: newView}
        } else {
            state
        }
    }

    action receiveMessages(node: Node, votes: Set[Vote], proposals: Set[Proposal]): bool = {
      val allProps = stateToAllProposals(protocolState, proposals)

      val pState = votes.fold(protocolState, (updatedState, vote) => {
        handleVote(vote, updatedState, node, allProps)
      })

      val pState1 = proposals.fold(pState, (updatedState, prop) => {
        handleProposal(prop, updatedState, node, allProps)
      })

      all {
        protocolState' = pState1,
        propAvailabilityLayer' = allProps,
      }
    }
    
    // New action to handle timeouts by synchronizing all correct nodes to the highest view
    action viewSync: bool = {

        val highestView = getHighestView(protocolState)
        val updatedState = allNodes.fold(protocolState, (pState, node) => {
            val newLocalState = updateToNewView(pState.get(node), highestView)
            pState.setBy(node, s => newLocalState)
        })


        val highestQC = correct.fold(genesisCert, (maxQC, node) => {
            val nodeState = updatedState.get(node)
            val nodeQC = nodeState.highQC
            match(nodeQC){
                |None => maxQC
                |Some(qc) => {
                    if (qc.block > maxQC.block) qc else maxQC
                }
            }
        })
        val lastCertifiedBlock = highestQC.block

        val epoch = if (lastCertifiedBlock % K == 0) lastCertifiedBlock / K else lastCertifiedBlock / K + 1
        val newLeader = leader(highestView + 1, epoch)
        // update the view of the new leader
        val newLeaderState = {...updatedState.get(newLeader), view: highestView + 1}
        val updatedState2 = updatedState.setBy(newLeader, state => newLeaderState)

        // update the cert to the 
        val NewProp = formProposal(newLeader, highestQC, newLeaderState)
        val newPropEpoch = if (NewProp.block % K == 0) NewProp.block / K else NewProp.block / K + 1
        val receivers =
            if (NewProp.block % K == 0){
                allNodes.filter(n => isInEpoch(n, newPropEpoch) or isInEpoch(n, newPropEpoch + 1))
            } else {
                allNodes.filter(n => isInEpoch(n, newPropEpoch))
            }
        val updatedStateWithProposal = multicastProposal(updatedState2, receivers, NewProp)

        all {
            protocolState' = updatedStateWithProposal,
            propAvailabilityLayer' = propAvailabilityLayer.union(Set(NewProp))
        }
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
        view: 0,
        highQC: None,
        highQCArchive: Map(),
        lockedQC: None,
        decidedQC: None,
        chain: List(),
        decidedQCArchive: List(),
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
        Triggers a timeout (viewSync).
    */
    action step = any {
        // Nondeterministically choose between normal message handling and timeout
        // view syncs only happen after the first block was committed
        val odds = 1.to(200)
        nondet timeout = oneOf(odds)

        if (timeout == 30){
            viewSync
        }
        else{   
            nondet n = oneOf(correct)
            val state = protocolState.get(n)

            val votes = state.votesBuffer.union(allFaultyVotes)
            nondet votesToReceive = votes.powerset().oneOf()

            val props = state.propsBuffer.union(allFaultyProposals)
            nondet propsToReceive = props.powerset().oneOf()

            receiveMessages(n, votesToReceive, propsToReceive)
        }
    }



    // quint run hotshot.qnt --invariant=noDeadlock to try to find an interesting counterexample
    // where this property doesn't hold
    val deadlock = not (protocolState.values().forall(s => size(s.votesBuffer) == 0 and size(s.propsBuffer) == 0))
    
    // Check that there is no deadlock when timeout mechanism is enabled
}

module hotshotTimeout {
  // Some arbitrary numbers, just to enable simulation
  import HotShotEpochReconfig(N = 4, F = 1, Q = 3, K = 5, MAX_NODES = 8, FAULTY = Set()).*
}