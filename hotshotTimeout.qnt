// -*- mode: Bluespec; -*-
module HotShotEpochReconfig {
    import types.* from "./types"
    import utils.* from "./utils"

    import communication.* from "./communication"

    import basicSpells.* from "spells/basicSpells"
    import commonSpells.* from "spells/commonSpells"
    import rareSpells.* from "spells/rareSpells"

    //// **Constants** (system parameters)
    const N: int         // total number of nodes (participants in consensus)
    const F: int         // fault tolerance threshold
    const Q: int         // quorum size (2F+1 signatures needed for decisions)
    const K: int         // epoch duration
    const MAX_NODES: int // size of the universe of node IDs (>= N, to allow new nodes joining)
    const FAULTY: Set[Node] // set of faulty nodes (size <= F)
    // list of validators for each epoch, each entry is a list of node IDs. 
    // the Node at index (j,i) is the leader of view i in epoch j (modulo the length of the list[j]).
    // The first 2 views should be led by the node 1 to be compatible with our current initialization.
    const VALIDATORS: List[List[Node]]


    pure val allNodes = 1.to(MAX_NODES)
    pure val correct: Set[Node] = allNodes.exclude(FAULTY)

    // This val is a set representation of the validators for each epoch.
    pure val stakingTables: List[StakingTable]= VALIDATORS.foldl(List(), (acc, l) => {
        val activeValidators = l.toSet()
        acc.append(activeValidators)
    })
        
    val allFaultyVotes : Set[Vote] = Set()
    val allFaultyProposals : Set[Proposal] = Set()
    
    // **Initial State Vals**
    val genesisCert = {
            cType: Quorum, 
            signers: Set(1, 2, 4), 
            nextEpochSigners: Set(),
            view: 0, 
            block: 0
        }

    val genesisProp = {
            sender: 1, 
            pType: Quorum, 
            view: 1, 
            block: 1, 
            certificate: genesisCert
        }

    // **State Variables**

    // the state of the protocol is represented as a map from node IDs to local states
    var protocolState: ProtocolState

    // A set to store all proposals, used to simulate fetchProposal from network
    var allProposals: Set[Proposal]


    // **Functions**

    /// Initialize the state of the system
    pure def initState: (ProtocolState, Set[Proposal]) = {

        val pState = 1.to(MAX_NODES).mapBy(node => {
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
            votesBuffer: Set(),
            propsBuffer: Set(genesisProp),
        })
        val allProps = Set(genesisProp)
        (pState, allProps)
    }
    
    
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
    pure def isLastBlockofEpoch(block: int) : bool = {
        block % K == 0
    }

    /// Return the epoch for a given block height
    pure def blockEpoch(block: int): int = {
        if (isLastBlockofEpoch(block)) block / K else block / K + 1
    }

    
    /// Return the epochs for which a node is active (only the current epoch or the current and next epoch)
    pure def getEpochs(node: Node, block: Block): Set[int] = {
        val epoch = blockEpoch(block)
        
    if (isLastBlockofEpoch(block)) //last block of the epoch
        Set(epoch, epoch+1).filter(e => isInEpoch(node, e))
    else 
        Set(epoch).filter(e => isInEpoch(node, e))
    }

    /// Check if a node is the leader for a given view and block
    pure def isLeader(node: Node, view: int, block: int): bool = {
        node == leader(view, blockEpoch(block))
    }

    /// Abstraction of signature validation
    pure def isSignatureValid: bool = {
        true
    }



    /// Check if a received vote is valid for a given node
    pure def isVoteValid(vote: Vote, node: Node, state: LocalState): bool = {
        val epoch = blockEpoch(vote.block)
        val validSignature = isSignatureValid

        and {
            vote.view >= state.view,
            validSignature,
            if (isLastBlockofEpoch(vote.block)) and {
                vote.vType != Extended implies (isLeader(node, vote.view+1, vote.block)),
                isInEpoch(node, epoch) or isInEpoch(node, epoch+1),
            }
            else and {
                isLeader(node, vote.view+1, vote.block),
                isInEpoch(node, epoch),
            }
        }

    }


    /// Abstraction tailored for simple simulations  
    pure def extends(a: Block, b: Block): bool = {
      a > b
    }

    /// Return a proposal record
    pure def proposal(node: Node, block: Block, view: int, pType: ProposalType, cert: Certificate): Proposal = {
        {sender: node, pType: pType, view: view, block: block, certificate: cert}
    }

    /// Return a vote record
    pure def vote(node: Node, block: Block, view: int, vType: VoteType): Vote = {
        {sender: node, vType: vType, view: view, block: block}
    }

    /// Return a certificate record for a given block, includes optional extra signers for the next epoch if the block is the last of the current epoch
    pure def certificate(node: Node, cType: CertificateType, view: int, block: Block, state: LocalState): Certificate = {
        val epoch = blockEpoch(block)

        val signers = state.votesMap.getOrElse((cType, block, view, epoch), Set())
        val basicCert = {cType: cType, signers: signers, nextEpochSigners: Set(),view: view, block: block}

        if (isLastBlockofEpoch(block)) { // Last block of the epoch
            val nextSigners = state.votesMap.getOrElse((cType, block, view, epoch + 1), Set())
            {...basicCert, nextEpochSigners: nextSigners}
        } else {
            basicCert
        }
    }


    /// Form a proposal based on a certificate.
    pure def formProposal(node: Node, cert: Certificate, state: LocalState): Proposal = {
        
        if (cert.block % K == 0 and cert.block > 0)  { // Last block of the epoch

            if (cert.cType == Extended) { // Extended proposal confirmed, propose the first block of the next epoch
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

    /// Check if the proposal respects the safety and liveness properties
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

    /// Check if the certificate included in the proposal is valid
    pure def isCertValid(proposal: Proposal, state: LocalState): bool = {
        val cert = proposal.certificate
        val block = proposal.block
        val epoch = blockEpoch(block)
        val isFirstBlock = (block % K == 1)
        
        if (isLastBlockofEpoch(block)){   // Last block of the epoch
            if (cert.cType == Extended) false
            // Check if the proposal with the repeated block (ie part of epoch change) has enough signatures for the current and next epoch
            else if (block == cert.block) and{ size(cert.signers.filter(s => isInEpoch(s,epoch))) >= Q , size(cert.nextEpochSigners.filter(s => isInEpoch(s,epoch+1))) >= Q} 
            else and {isProposalSafe(proposal,state) , size(cert.signers.filter(s => isInEpoch(s,epoch))) >= Q}
        }

        else if (isFirstBlock and block !=1 ){ // First block of the epoch and not the genesis block, special treatment for the first block to ensure the system starts progressing
            if (cert.cType != Extended) false
            else if (not(isProposalSafe(proposal, state))) false
            else and {size(cert.signers) >= Q , (size(cert.nextEpochSigners) >= Q)}
        }

        else { // Not first or last block of the epoch
            if (cert.cType == Extended) false
            else if (not(isProposalSafe(proposal, state))) false
            else if (not(size(cert.signers.filter(s => isInEpoch(s,epoch))) >= Q)) false
            else true
        }
    }

    // Check if the extended proposal is valid
    pure def isExtendedProposalValid(proposal: Proposal, state: LocalState, node: Node): bool = and {
        state.highQC != None,
        val highQC = state.highQC.unwrap()

        or {
            and {//this is a trick to avoid a node updating it's QC and rejecting it's own proposal
                proposal.sender == node,
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

    pure def isProposalValid(state: LocalState, proposal: Proposal, node: Node): bool = { 
        and {
            proposal.view >= state.view,
            isSignatureValid,
            isLeader(proposal.sender, proposal.view, proposal.block),
            proposal.pType == Extended implies isExtendedProposalValid(proposal, state, node),
            isCertValid(proposal, state),
        }
    }

    
    /// Utility function to update the stored chain
    pure def updateChain(node: Node,oldChain: int -> List[Block], newBlocks: List[Certificate]): int -> List[Block] = {
        val chainMap = newBlocks.foldl(oldChain, (cm, c) => {
            val epoch = c.block / K + 1
            val x = cm.has(epoch)
            if (x) cm.setBy(epoch, chain => chain.append(c.block))
            else cm.put(epoch, List(c.block))
        })
        val goodEpochs = chainMap.keys().filter(e => not (isInEpoch(node, e)))
        chainMap.mapRemoveAll(goodEpochs)
    }

    /// Update the stored quorum certificates (high-locked-decided) in the local state based on the last observed
    /// valid certificate and commit the decided blocks to the chain. 
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

                            // the last block of the epoch is commited by the nodes of epoch+1
                            val epoch = justify2HighQC.block / K + 1
                            val nodeInEpoch = isInEpoch(node, epoch)
                            val newBlocks = commitedBlocks(justify2HighQC, decidedQC, state.highQCArchive)
                            val newHighQCArchive = mapRemoveAll(state.highQCArchive, toSet(newBlocks).map(c => c.block))
                            val chainMap = updateChain(node, state.chain, newBlocks)
                            { ...state, highQC: Some(highQC), lockedQC: Some(justifyHighQC), decidedQC: Some(justify2HighQC) , highQCArchive:newHighQCArchive, chain: chainMap}
                        } else if (updateLockedQC){
                            { ...state, highQC: Some(highQC), lockedQC: Some(justifyHighQC)}
                        } else if (updateDecidedQC){  
                            val epoch = justify2HighQC.block / K + 1
                            val nodeInEpoch = isInEpoch(node, epoch)
                            
                            val newBlocks = commitedBlocks(justify2HighQC, decidedQC, state.highQCArchive)
                            val newHighQCArchive = mapRemoveAll(state.highQCArchive, toSet(newBlocks).map(c => c.block))
                            val chainMap = updateChain(node, state.chain, newBlocks)
                            { ...state, highQC: Some(highQC), decidedQC: Some(justify2HighQC), highQCArchive:newHighQCArchive, chain: chainMap}
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
        val epochs = getEpochs(vote.sender, vote.block)

        // For each relevant epoch, add the voter to the votes map
        val newVotes = epochs.fold(state.votesMap, (newVotesMap, e) => {
            val key = (vote.vType, vote.block, vote.view, e)
            newVotesMap.setByWithDefault(key, voters => voters.union(Set(vote.sender)).filter(s => isInEpoch(s,e)), Set())
        })
        { ...state, votesMap: newVotes }
    }

    /// Check if a quorum of votes has been reached for a proposal based on the accumulated votes
    pure def thresholdReached(vote: Vote, state: LocalState): bool = {
        val epochs = if (vote.block % K == 0) Set(vote.block / K, vote.block / K + 1) else Set(vote.block / K + 1)
        
        // For each relevant epoch, check if we have enough votes
        epochs.forall(e => {
                val key = (vote.vType, vote.block, vote.view, e)
                val voters = state.votesMap.getOrElse(key, Set())
                voters.size() >= Q
            })
    }

    /// Send a proposal to the leader (either the current leader or the next epoch leader)
    pure def sendVoteToLeader(state: ProtocolState, v: Node, vote: Vote): ProtocolState = {
        pure val epoch = if (vote.block % K == 0) vote.block / K else vote.block / K + 1
        pure val localState = state.get(v)

        pure val leaderToSend = if (vote.vType == Extended) {
          leader(localState.view + 1, epoch + 1)
        } else {
          leader(localState.view + 1, epoch)
        }
        sendVote(state, leaderToSend, vote)
    }

    /// Handle a vote message by updating the local state of the node and possibly sending a proposal.
    pure def handleVote(vote: Vote, pState: ProtocolState, node: Node, allProps: Set[Proposal]): ProtocolState = {
        val oldState = pState.get(node)
        val state = { ...oldState, votesBuffer: oldState.votesBuffer.exclude(Set(vote)), voteArchive: oldState.voteArchive.union(Set(vote))}
        val epoch = blockEpoch(vote.block)
        val nodes = pState.keys()

        
        if (isVoteValid(vote, node, state)){
            val stateWithSig = accumulateSignatures(vote, state)

            if (thresholdReached(vote, stateWithSig)){
                // Form a certificate
                val cert = certificate(node, vote.vType, vote.view, vote.block, stateWithSig)
                val stateWithCerts = updateCerts(node ,stateWithSig, cert, allProps)
                val newView = cert.view + 1
                val newState = { ...stateWithCerts, view: newView }
                
                // This is a trick to avoid duplicating the code from formProposal,
                // We use the "potential" new proposal to check if we have passed to the next epoch or not 
                val newProp = formProposal(node, cert, newState)
                val newPropEpoch = blockEpoch(newProp.block)

                if (node == leader(newProp.view, newPropEpoch)){
                    // Update certificates based on the proposal's certificate
                    val receivers =
                        if (isLastBlockofEpoch(newProp.block)) {
                            // If the proposal is the last block of the epoch, send to all nodes in the current and next epoch
                            nodes.filter(n => isInEpoch(n, newPropEpoch) or isInEpoch(n, newPropEpoch + 1))
                        } else {
                            nodes.filter(n => isInEpoch(n, newPropEpoch))
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

    /// Handle a proposal message by updating the local state of the node and possibly sending a vote.
    pure def handleProposal(prop: Proposal, pState: ProtocolState, node: Node, allProps: Set[Proposal]): ProtocolState = {
        val oldState = pState.get(node)
        val state = { ...oldState, propsBuffer: oldState.propsBuffer.exclude(Set(prop)), proposalArchive: oldState.proposalArchive.union(Set(prop))}
        val nodes = pState.keys()
        
        if (isProposalValid(state, prop, node)){
            val stateWithcerts = updateCerts(node, state, prop.certificate, allProps)
            val newView = prop.view
            val newState = { ...stateWithcerts, view: newView}
            val newVote = vote(node, prop.block, prop.view, prop.pType)
            val newPstate = pState.setBy(node, state => newState)

            if (prop.pType == Extended){ //if the prop is an extended vote
                val receivers = nodes.filter(n => isInEpoch(n, prop.block / K + 1))
                multicastVote(newPstate, receivers, newVote)
            } else {    
                sendVoteToLeader(newPstate, node, newVote)
            }
            
        } else {
            pState.setBy(node, s => state)
        }
    }

    /// Utility function to accumulate all proposals from the protocol state. Used to simulate fetchProposal from network.
    pure def accumulateProposals(pState: ProtocolState, allProps: Set[Proposal]): Set[Proposal] = {
        pState.values().fold(allProps, (props, state) => {
            props.union(state.propsBuffer).union(state.proposalArchive)
        })
    }

    /// Get the highest view number among all correct nodes
    pure def getHighestView(pState: ProtocolState): int = {
        correct.fold(0, (maxView, node) => {
            val nodeView = pState.get(node).view
            if (nodeView > maxView) nodeView else maxView
        })
    }

    /// Non deterministic action to simulate message delivery via network under the assumption of partial synchrony.
    action deliverMessages(node: Node, votes: Set[Vote], proposals: Set[Proposal]): bool = {
      val allProps = accumulateProposals(protocolState, proposals)

      val pState = votes.fold(protocolState, (updatedState, vote) => {
        handleVote(vote, updatedState, node, allProps)
      })

      val pState1 = proposals.fold(pState, (updatedState, prop) => {
        handleProposal(prop, updatedState, node, allProps)
      })

      all {
        protocolState' = pState1,
        allProposals' = allProps,
      }
    }
    
    /// This action abstracts away viewSync and brings all correct nodes to the highest view  
    action viewSync: bool = {
        
        // find the highest view among all correct nodes
        val highestView = getHighestView(protocolState)
        val nodes = protocolState.keys()

        // update the state of all nodes to the highest view
        val updatedState = nodes.fold(protocolState, (pState, node) => {
            val newLocalState = updateToNewView(pState.get(node), highestView)
            pState.setBy(node, s => newLocalState)
        })

        // leader collects the highest QC from all correct nodes
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
        val epoch = blockEpoch(lastCertifiedBlock)
        
        // leader of the next view proceeds to propose a new block
        val newLeader = leader(highestView + 1, epoch)
        // update the view of the new leader
        val newLeaderState = {...updatedState.get(newLeader), view: highestView + 1}
        val updatedState2 = updatedState.setBy(newLeader, state => newLeaderState)
        
        // form a new proposal
        val newProp0 = formProposal(newLeader, highestQC, newLeaderState)
        // if the new proposal is an extended proposal, restart the 3 successive certs procedure
        val newProp = if (newProp0.pType == Extended) { 
            proposal(newLeader, highestQC.block, highestView + 1, Quorum, highestQC)
        } else {
            newProp0
        }
        
        val newPropEpoch = blockEpoch(newProp.block)
        val receivers =
            if (isLastBlockofEpoch(newProp.block)) {
                nodes.filter(n => isInEpoch(n, newPropEpoch) or isInEpoch(n, newPropEpoch + 1))
            } else {
                nodes.filter(n => isInEpoch(n, newPropEpoch))
            }
        val updatedStateWithProposal = multicastProposal(updatedState2, receivers, newProp)

        all {
            protocolState' = updatedStateWithProposal,
            allProposals' = allProposals.union(Set(newProp))
        }
    }
    
    // **Actions**


    /// Initialize the state of the system
    action init = all {
        protocolState' = initState._1,
        allProposals' = initState._2,
    }



   
    /// Execution Loop
    /// The execution step (step) randomly picks a validator and either:
    /// Delivers a pending message (deliver).
    /// Triggers a (viewSync).
    action step = {
        // Nondeterministically choose between normal message handling and view synchronization with a skew towards normal steps so the system is more likely to
        // make progress
        val odds = 1.to(100)
        nondet timeout = oneOf(odds)

        // The view sync occurs with a probabiliy of 1%
        if (timeout == 1){
            viewSync
        } else {   
            stepWithoutTimeout
        }
    }

    /// Execution step without viewSync
    action stepWithoutTimeout = {        
            nondet n = oneOf(correct)
            val state = protocolState.get(n)

            val votes = state.votesBuffer.union(allFaultyVotes)
            nondet votesToReceive = votes.powerset().exclude(Set(Set())).oneOf()

            val props = state.propsBuffer.union(allFaultyProposals)
            nondet propsToReceive = props.powerset().exclude(Set(Set())).oneOf()

            deliverMessages(n, votesToReceive, propsToReceive)     
    } 



    
    
    /// A witness that is violated when there are no pending messages in the system, meaning that the system is not making progress
    /// and is stuck in a deadlock.
    /// This check is specific to our modelling of the protocol, and it relies on the fact that no timeouts/transmission mechanism was
    /// included in the system. 
    /// This property doesn't fully cover the liveness property, as it doesn't take into account the possibility of a livelock.
    
    val deadlock = not (protocolState.values().forall(s => size(s.votesBuffer) == 0 and size(s.propsBuffer) == 0))
    /*
    After checking this invariant, we discovered an issue with highQC field that is used to check the validity of extended certificates 
    (a check on 3 consecutive views with proposal.view - 1 = proposal.cert.view and proposal.cert.view - 1 = state.highQC). 
    The problem here is that upon reaching the threshold for votes for the quorum proposal that precedes the extended proposal, 
    the leader will form a quorum certificate and store it as highQC (function updateCerts is called in the main loop). 
    This will cause the leader to reject it’s own proposal because the 3 consecutive views rule does not hold anymore 
    (given that highQC was updated when forming the QC). 
    As a consequence, a leader will not validate it’s own extended proposal and this creates a deadlock. 
    This problem was not observed in the code.
    */



    /// If a node transitions to the next epoch (ie extended Quorum cert was formed) while other nodes are still in the current epoch,
    /// the nodes in the current epoch should have received the votes for extended QC.
    /// Apply this only on nodes that are part of e / e+1
    val transition = not (
        // some nodes are already in the next epoch
        protocolState.values().exists(s => s.highQC != None and s.highQC.unwrap().block == K and s.highQC.unwrap().cType == Extended)
        and
        // the nodes in the current epoch have not received the votes for extended QC
        {
        val nodes2 = protocolState.keys().filter(n => isInEpoch(n,2))
        val states2 = nodes2.map(n => protocolState.get(n))
        states2.exists(s => s.highQC != None and  
                                    s.highQC.unwrap().block == K 
                                    and s.highQC.unwrap().cType == Quorum 
                                    and s.votesBuffer.filter(v => v.block == K and v.vType == Extended).size()==0  
                                    //some nodes might receive the proposal with the QC from the leader before receiving the votes
                                    and s.propsBuffer.filter(p => p.certificate.block == K and p.certificate.cType == Extended).size()==0) 
        }
    )
    /*
    After checking this invariant, we found that step 6 of the specs text explicitly requires nodes to send V_{v+2}ˆextended votes 
    to all nodes in epoch e+1. However, the pseudocode implementation only reflects votes being transmitted to the leader, 
    as it can be seen in the sendVote(vote) function.
    */


    /// A witness to generate a run where a transition into epoch 2 occured. It can be used
    /// to let the simulator generate an optimal scenario (as described in the English spec)
    /// using the stepWithoutTimeout action
    val optimalRun = not (protocolState.values().exists(s => s.decidedQC != None and s.decidedQC.unwrap().block == K + 1))

    /// A witness that allows us to let the simulator find runs where a timeout occurs in the epoch change
    /// using the standard step action. As the optimal runs needs 3 proposals, we look for a state with 
    /// 4 proposals.
    val timeoutEpochRun = not (
        // we moved to the next epoch
        // At least one node has a decided QC for the first block of the next epoch
        protocolState.values().exists(s => s.decidedQC != None and s.decidedQC.unwrap().block == K + 1)
        and
        // block K was proposed more than 3 times, this comes from the fact that view change needs to restart if interrupted
        // by a view sync, resulting in the block of height K being reproposed to build the 3 chain extended cert
        protocolState.values().exists(s => s.proposalArchive.filter(p => p.block == K).size() > 3)

        and
        // for all other blocks (1.to(K-1)) the block was proposed only once on all nodes to avoid viewSyncs before the epoch change
        // this can be eliminated because the simulations tend to find a case that fits this naturally
        1.to(K-1).forall(b => {
            protocolState.values().forall(s => {
                val props = s.proposalArchive.filter(p => p.block == b)
                if (props.size() > 1) {
                    false
                } else {
                    true
                }
            })
        })
    )
}

module hotshotTimeout {
  // V is a list of lists, where each inner list represents the validators for a specific epoch
  // The first 2 views should be led by the node 1 to be compatible with our current initialization.
  // Look at the VALIDATOR CONSTANTS in the HotShotEpochReconfig module for more details.
  val V = List(
            List(1, 1, 2, 3, 4, 1, 2, 3, 4),
            List(2, 6, 7, 1),
            List(1, 2, 4, 5),
            List(1, 5, 6, 8),
            List(2, 3, 4, 5)
        )
  import HotShotEpochReconfig(N = 4, F = 1, Q = 3, K = 5, MAX_NODES = 8, FAULTY = Set(), VALIDATORS = V).*
}