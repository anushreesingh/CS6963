open util/integer

sig Term {}

sig Node {
	votedFor: Node lone -> Term
}

fun leaders(te: Term): set Node {
	{n: Node | #votedFor.te.n > div[#Node,2]}
}

pred show() {}

run show for 3 Term, 3 Node, 10 Int

assert atMostOneLeader {
	all te: Term | lone leaders[te]
}

check atMostOneLeader for 3 Term, 5 Node, 7 Int
/*
assert atLeastOneLeader {
	one leaders
}

check atLeastOneLeader for 3 Node, 7 Int
*/
