// -*- mode: Bluespec; -*-
module communication{
  import basicSpells.* from "spells/basicSpells"
  import types.* from "./types"

  /* MESSAGE PASSING FUNCTIONS */

  pure def multicastProposal(receivers: Set[Node], proposal: Proposal): Set[Message] = {
    receivers.map(n => { destinatary: n, message: ProposalMessage(proposal) })
  }

  pure def multicastVote(receivers: Set[Node], vote: Vote): Set[Message] = {
    receivers.map(n => { destinatary: n, message: VoteMessage(vote) })
   }

  pure def sendVote(receiver: Node, vote: Vote): Set[Message] = {
    Set({ destinatary: receiver, message: VoteMessage(vote) })
  }

  pure def getProposals(s: Set[Message]): Set[Proposal] = {
    s.fold(Set(), (acc, e) => {
      match e.message {
        | ProposalMessage(p) => acc.union(Set(p))
        | _ => acc
      }
    })
  }

  pure def getVotes(s: Set[Message]): Set[Vote] = {
    s.fold(Set(), (acc, e) => {
      match e.message {
        | VoteMessage(v) => acc.union(Set(v))
        | _ => acc
      }
    })
  }
}
