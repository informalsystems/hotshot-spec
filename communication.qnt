module communication{

    import types.* from "./types"
    export types.*

    //// ** MESSAGE PASSING FUNCTIONS **
    pure def broadcastProposal(state : ProtocolState, receivers: Set[Node], proposal: Proposal):ProtocolState = {
        state
    }

    pure def sendVote(state : ProtocolState, receivers: Set[Node], vote: Vote):ProtocolState = {
        state
    }

    pure def sendByzantineVote(state : ProtocolState, receivers: Set[Node]):ProtocolState = {
        state
    }

    pure def broadcastByzantineProposal(state : ProtocolState, receivers: Set[Node]):ProtocolState = {
        state
    }

    pure def handleVotes(state : ProtocolState, vote: Vote, receiver:Node):ProtocolState = {
        state
    }

    pure def handleProposals(state : ProtocolState, proposal: Proposal, receiver:Node):ProtocolState = {
        state
    }
}