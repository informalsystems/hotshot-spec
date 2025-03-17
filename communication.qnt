module communication{

    import types.* from "./types"
    export types.*

    //// ** MESSAGE PASSING FUNCTIONS **
    pure def broadcastProposal(state : ProtocolState, proposal: Proposal):ProtocolState = { //THIS PROBABLY WON'T BE USED
        state.keys().mapBy(p => {
            val nodeState = state.get(p)
            val newProposals = nodeState.proposals.union(Set(proposal))
            { ...nodeState, proposals: newProposals }
        })
    }

    pure def multicastProposal(state : ProtocolState, receivers: Set[Node], proposal: Proposal):ProtocolState = {
        receivers.mapBy(r => {
            val nodeState = state.get(r)
            val newProposals = nodeState.proposals.union(Set(proposal))
            { ...nodeState, proposals: newProposals }
        })
    }

    pure def sendProposal(state : ProtocolState, receiver: Node, proposal: Proposal):ProtocolState = {
        val nodeState = state.get(receiver)
        val newProposals = nodeState.proposals.union(Set(proposal))
        state.put(receiver, { ...nodeState, proposals: newProposals })
    }

    pure def broadcastVote(state : ProtocolState, vote: Vote):ProtocolState = { //THIS PROBABLY WON'T BE USED
        state.keys().mapBy(p => {
            val nodeState = state.get(p)
            val newVotes = nodeState.votes.union(Set(vote))
            { ...nodeState, votes: newVotes }
        })
    }

    pure def multicastVote(state : ProtocolState, receivers: Set[Node], vote: Vote):ProtocolState = {
        receivers.mapBy(r => {
            val nodeState = state.get(r)
            val newVotes = nodeState.votes.union(Set(vote))
            { ...nodeState, votes: newVotes }
        })
    }

    pure def sendVote(state : ProtocolState, receiver: Node, vote: Vote):ProtocolState = {
        val nodeState = state.get(receiver)
        val newVotes = nodeState.votes.union(Set(vote))
        state.put(receiver, { ...nodeState, votes: newVotes })
    }

    pure def sendByzantineVote(state : ProtocolState, receivers: Set[Node]):ProtocolState = { //TODO
        state
    }

    pure def broadcastByzantineProposal(state : ProtocolState, receivers: Set[Node]):ProtocolState = { //TODO
        state
    }
}