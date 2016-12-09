open util/integer
open util/ordering[Time] as to

sig Time {}

abstract sig Role {}

one sig Candidate, Follower, Leader extends Role {}

sig Node {
	role: Role one -> Time,
	votedFor: Node -> Time
}

fact onlyOneVote {
	all n: Node | (lone n.votedFor.Time and lone Node.(n.votedFor))
}

fact onlyCandidatesReceiveVotes {
	all n: Node, t: Time | n.votedFor.t.role.t in Candidate
}

fact defineElected {
	all n: Node, t: Time |
		n.role.t = Leader <=> (#votedFor.(to/prevs[t]).n > div[#Node, 2])
}

fact candidatesOnlyVoteForSelf {
	all n: Node | (Candidate in n.role.Time <=> n in n.votedFor.Time)
}


// Everyone starts out as a follower with no votes cast yet and noone elected
pred init(t: Time) {
	no Node.votedFor.t
	Node.role.t = Follower
}

fact traces {
	init [to/first]
}


pred show() {
	some n: Node, t: Time | n.role.t = Leader
	#Node = 5
	#votedFor >5
}

run show for 5 Node, 5 Int, 10 Time

assert atMostOneLeader {
	lone {n: Node | Leader in n.role.Time}
}

check atMostOneLeader for 5 Node, 5 Int, 10 Time
