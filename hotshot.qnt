module HotShotEpochReconfig {

    import types.* from "./types"
    export types.*

    import communication.* from "./communication"
    export communication.*

    //// **Constants** (system parameters)
    const N: int                      // total number of nodes (participants in consensus)
    const F: int                      // fault tolerance threshold (max number of Byzantine faults)
    const Q: int         /// quorum size (2F+1 signatures needed for decisions)&#8203;:contentReference[oaicite:0]{index=0}
    const K: int         // duration of an epoch
    const TIMEOUT_DELAY: int          // maximum waiting time (in protocol steps) before triggering a timeout
    const MAX_NODES: int              // size of the universe of node IDs (>= N, to allow new nodes joining)


    //  Revise, this is only for protoyping
    pure val allNodes = 1.to(MAX_NODES)
    pure val stakingTables: List[StakingTable]= List()
    const Faulty: Set[Node]
    //val correct = allNodes - Faulty

    var protocolState: ProtocolState
    
    
    //// **Local pure functions** (helpers for logic, no state modification)

    //
    // Verification & validity functions
    //

    pure def isInEpoch(node: Node, epoch: int): bool = //TODO: implement epoch check
        true
    
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


    pure def isProposalSafe(proposal: Proposal, node:Node, state:LocalState): bool =
        or {
            proposal.block > state.lockedQC.block,// Safety Rule (TODO: rewrite using extend)
            proposal.certificate.view > state.lockedQC.view //Liveness Rule
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

    pure def isExtendedProposalValid(proposal: Proposal, node: Node, state: LocalState): bool = {//TODO: implement extended proposal verification
        val hightQC = state.highQC
        if ((proposal.block != proposal.certificate.block) or (proposal.block != hightQC.block)) false
        else if ((proposal.view-1 != proposal.certificate.view) or (proposal.certificate.view-1 != hightQC.view)) false
        else true
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

    pure def updateCerts



    // Message Sending via adding them to buffers using pure def functions
    // Message delivery via actions
    /*
    Moves the vote from voteBuffer to incomingVotes.
    action deliverVote(v: Address, vote: Vote) : bool = all {
        voteBuffer.get(v).union(AllFaultyVotes).contains(vote), 
        voteBuffer' = voteBuffer.put(v, voteBuffer.get(v).exclude(Set(vote))),
        system' = system.put(v, { ...system.get(v), incomingVotes: system.get(v).incomingVotes.union(Set(vote)) }),
        _hist' = _hist,
        propBuffer' = propBuffer, 
        certBuffer' = certBuffer,
    }

    Non-deterministically chooses a message type (proposal, vote, or certificate).
    Delivers it to the validator
    action deliver(v: Address) : bool = any {
        val props = propBuffer.get(v).union(AllFaultyProposals)
        all{
            props.size() > 0,
            nondet prop = oneOf(props)
            deliverProposal(v, prop),
        },
        val votes = voteBuffer.get(v).union(AllFaultyVotes)
        all {
            votes.size() > 0,
            nondet vote = oneOf(votes)
            deliverVote(v, vote),
        },
        deliverSomeCertificate(v)
    }

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
    }

    Execution Loop
    The execution step (step) randomly picks a validator and either:
        Executes a consensus step (valStep).
        Delivers a pending message (deliver).
        Sets a new value to propose (setNextValueToPropose).

    action step = {
        nondet v = oneOf(Correct)
        nondet value = oneOf(Values)
        any {
            valStep(v),
            deliver(v),
            setNextValueToPropose(v, value),
        }
    }


    */


    //// **Actions** (state transitions)
    /// Initialize the system state (epoch 0 with initial membership)
    action init = all {
        protocolState' = allNodes.mapBy(n => {
        epoch: 0,
        view: 0,
        highQC: {which: NoneC, signers: Set(), view: 0, block: 0},
        lockedQC: {which: NoneC, signers: Set(), view: 0, block: 0},
        //isActive: true,
        //isLeader: false,
        //leader: 0,
        proposals: Set(),
        votes: Set()
        })
    }

    /// Start an epoch reconfiguration when conditions are met (epoch end or stake update)
    action proposeLastBlock = all {
    protocolState' = allNodes.mapBy(n => {
        epoch: 0,
        view: 0,
        highQC: {which: NoneC, signers: Set(), view: 0, block: 0},
        lockedQC: {which: NoneC, signers: Set(), view: 0, block: 0},
        //isActive: true,
        //isLeader: false,
        //leader: 0,
        proposals: Set(),
        votes: Set()
        })
    } // TODO
        
}
