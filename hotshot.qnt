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
    pure val stakingTables: List[StakingTable]=List(
    // First epoch staking table: nodes 1, 2, 4, 5 are active
    Set(1, 2, 4, 5),
    // Second epoch staking table: nodes 1, 2, 4, 6 are active
    Set(1, 2, 3, 6),
    )
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


    pure def isVoteValid2(vote: Vote, node: Node, state: LocalState): bool = {
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

    pure def isVoteValid(vote: Vote, node: Node, state: LocalState): bool = {
        true
    }

    pure def extends(a: Block, b: Block): bool = {
      // In a blockchain, block a extends block b if a has a higher height than b
      // and a is built on top of b (directly or indirectly)
      // Since we're only storing block height currently, we check if a > b
      a > b
    }

    pure def proposal(node: Node, block: Block, view: int, which: ProposalType, cert: Certificate): Proposal = { //TODO: allProps is a hack, need to fix
        {sender: node, which: Quorum, view: view, block: block, certificate: cert}
    }

    pure def vote(node: Node, block: Block, view: int, which: VoteType): Vote = {
        {sender: node, which: which, view: view, block: block}
    }

    pure def certificate(node: Node, which: CertificateType, view: int, block: Block, state: LocalState): Certificate = {
        val lastBlock = (block % K == 0)
        val epoch = block / K
        val signers = state.votesMap.getOrElse((which, block, view, state.epoch), Set())
        val basicCert = {which: which, signers: signers, nextEpochSigners: Set(),view: view, block: block}
        if (lastBlock){
            val extraSigners = state.votesMap.getOrElse((which, block, view, state.epoch + 1), Set())
            {...basicCert, nextEpochSigners: extraSigners}
        } else {
            basicCert
        }
    }




    pure def formProposal(node: Node, cert: Certificate): Proposal = {
        if (cert.block % K == 0) {
            if (cert.which == Extended) {
                val newType = Quorum
                val newBlock = cert.block + 1  // obtain a new block
                proposal(node, newBlock, cert.view + 1, newType, cert)
            }
            else {
                val newBlock = cert.block
                val localState = protocolState.get(node)
                val newType = 
                    if (localState.highQC != None and localState.lockedQC != None) {
                        val highQC = localState.highQC.unwrap()
                        val lockedQC = localState.lockedQC.unwrap()
                        if (and {highQC.block == lockedQC.block
                            , cert.view - 1 == highQC.view
                            , highQC.view - 1 == lockedQC.view}){
                            Extended
                        } else {
                            Quorum
                        }
                    } else {
                        Quorum
                    }
                val newView = cert.view + 1
                proposal(node, newBlock, newView, newType, cert)
            }
        }
        else {
            val newBlock = cert.block + 1
            val newView = cert.view + 1
            proposal(node, newBlock, newView, Quorum, cert)
        }
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

    pure def isProposalValid2(state: LocalState, proposal: Proposal): bool = {
        if (proposal.view < state.view) false
        else if (not(isSignatureValid(0))) false //TODO: args need to be changed
        else if (not(isLeader(proposal.sender, proposal.view, proposal.block))) false
        else if ((proposal.which == Extended) and (not(isExtendedProposalValid(proposal, proposal.sender, state))))
        false
        else if (not (isJustifyCertValid(proposal, proposal.sender, state))) false
        else true
    }

    pure def isProposalValid(state: LocalState, proposal: Proposal): bool = {
       true
    }

    pure def fetchProposal(cert:Certificate, propDA: Set[Proposal]): Option[Proposal] = {
        //return the proposal that has the certificate
        propDA.find(prop => prop.block == cert.block)
    }

    // To be removed
    pure def certOrNeg(cert: Option[Certificate]): Certificate = {
        match(cert){
            |None => {which: Quorum, signers: Set(), nextEpochSigners: Set(),view: -1, block: -1}
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
                    val updateLockedQC =  and {highQC.view - 1 == justifyHighQC.view, justifyHighQC.view > lockedQC.view}
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
            newVotesMap.setByWithDefault(key, voters => voters.union(Set(vote.sender)), Set())
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
            protocolState' = protocolState.setBy(n, state => { ...state, votesBuffer: newVotesBuffer, votes: newVotes }),
            propAvailabilityLayer' = propAvailabilityLayer //TODO: This is a hack, need to fix
        }
    }

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


    pure def handleVote(vote: Vote, pState: ProtocolState, node: Node, allProps: Set[Proposal]): ProtocolState = {
        val oldState = pState.get(node)
        val state = { ...oldState, votes: oldState.votes.exclude(Set(vote)), voteArchive: oldState.voteArchive.union(Set(vote))}

        if (isLeader(node,state.view, state.epoch)){
            if (isVoteValid(vote, node, state)){
                val updatedState = accumulateSignatures(vote, node, state)
                if (threshholdReached(vote, updatedState)){
                    // Form a certificate
                    val cert = certificate(node, vote.which, vote.view, vote.block, state)
                    val stateWithCerts = updateCerts(updatedState, cert, allProps)
                    val newView = cert.view + 1
                    val newState = { ...stateWithCerts, view: newView }
                    // Form a proposal
                    val prop = formProposal(node, cert)
                    // Update certificates based on the proposal's certificate
                    broadcastProposal(pState.setBy(node, state => newState), prop)
                } else {
                    // Do nothing
                    pState.setBy(node, state => updatedState)
                }

            } else {
                // Do nothing
                pState
            }

        }else {

            if (isVoteValid(vote, node, state)){
                val updatedState = accumulateSignatures(vote, node, state)
                if (threshholdReached(vote, updatedState)){
                    // Form a certificate
                    val cert = certificate(node, vote.which, vote.view, vote.block, state)
                    val stateWithCerts = updateCerts(updatedState, cert, allProps)
                    val newView = cert.view + 1
                    val newState = { ...stateWithCerts, view: newView }
                    // Update certificates based on the proposal's certificate
                    pState.setBy(node, state => newState)
                } else {
                    // Do nothing
                    pState.setBy(node, state => updatedState)
                }

            } else {
                // Do nothing
                pState
            } 

        }
    }

    pure def handleProposal(prop: Proposal, pState: ProtocolState, node: Node, allProps: Set[Proposal]): ProtocolState = {
        val oldState = pState.get(node)
        val state = { ...oldState, proposals: oldState.proposals.exclude(Set(prop)), proposalArchive: oldState.proposalArchive.union(Set(prop))}
        
        if (isProposalValid(state, prop)){
            val stateWithcerts = updateCerts(state, prop.certificate, allProps)
            val newView = prop.view
            val newState = { ...stateWithcerts, view: newView}
            // remove the proposal from the state
            val newVote = vote(node, prop.block, prop.view, prop.which)
            val newPstate = pState.setBy(node, state => newState)
            sendVoteToLeader(newPstate, node, newVote)
        } else {
            pState
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
        epoch: 0,
        view: 0,
        highQC: None,
        lockedQC: None,
        decidedQC: None,
        proposals: Set(),
        votes: Set(),
        proposalArchive: Set(),
        voteArchive: Set(),
        votesMap: Map(),
        votesBuffer: Set(),
        propsBuffer: if (node != 1) Set(genesisProp) else Set(),
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
    // Doesn't find any yet because we aren't generating any valid proposals
    val witness = true
}

module hotshot {
  // Some arbitrary numbers, just to enable simulation
  import HotShotEpochReconfig(N = 4, F = 1, Q = 3, K = 100000, TIMEOUT_DELAY = 4, MAX_NODES = 7, Faulty = Set()).*
}
