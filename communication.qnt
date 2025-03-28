// -*- mode: Bluespec; -*-
module communication{
    import basicSpells.* from "spells/basicSpells"
    import types.* from "./types"

    //// ** MESSAGE PASSING FUNCTIONS **
    pure def broadcastProposal(state : ProtocolState, proposal: Proposal):ProtocolState = { //THIS PROBABLY WON'T BE USED
        state.keys().mapBy(p => {
            val nodeState = state.get(p)
            val newpropsBuffer = nodeState.propsBuffer.union(Set(proposal))
            { ...nodeState, propsBuffer: newpropsBuffer }
        })
    }

    pure def multicastProposal(state : ProtocolState, receivers: Set[Node], proposal: Proposal):ProtocolState = {
        state.keys().mapBy(p => {
            if (receivers.contains(p)) {
                val nodeState = state.get(p)
                val newpropsBuffer = nodeState.propsBuffer.union(Set(proposal))
                { ...nodeState, propsBuffer: newpropsBuffer }
            } else {
                state.get(p)
            }
        })
    }

    pure def sendProposal(state : ProtocolState, receiver: Node, proposal: Proposal):ProtocolState = {
        val nodeState = state.get(receiver)
        val newpropsBuffer = nodeState.propsBuffer.union(Set(proposal))
        state.put(receiver, { ...nodeState, propsBuffer: newpropsBuffer })
    }

    pure def broadcastVote(state : ProtocolState, vote: Vote):ProtocolState = { //THIS PROBABLY WON'T BE USED
        state.transformValues(nodeState => {
            val newvotesBuffer = nodeState.votesBuffer.union(Set(vote))
            { ...nodeState, votesBuffer: newvotesBuffer }
        })
    }

    pure def multicastVote(state : ProtocolState, receivers: Set[Node], vote: Vote):ProtocolState = {
        receivers.mapBy(r => {
            val nodeState = state.get(r)
            val newvotesBuffer = nodeState.votesBuffer.union(Set(vote))
            { ...nodeState, votesBuffer: newvotesBuffer }
        })
    }

    pure def sendVote(state : ProtocolState, receiver: Node, vote: Vote):ProtocolState = {
        val nodeState = state.get(receiver)
        val newvotesBuffer = nodeState.votesBuffer.union(Set(vote))
        state.put(receiver, { ...nodeState, votesBuffer: newvotesBuffer })
    }

    pure def sendByzantineVote(state : ProtocolState, receivers: Set[Node]):ProtocolState = { //TODO: IS THIS NEEDED?
        state
    }

    pure def broadcastByzantineProposal(state : ProtocolState, receivers: Set[Node]):ProtocolState = { //TODO: IS THIS NEEDED?
        state
    }
}
