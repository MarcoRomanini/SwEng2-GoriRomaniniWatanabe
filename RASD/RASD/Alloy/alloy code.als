// User (Farmer, Agronomist, PolicyMaker)
abstract sig User {
	userID: one Int,
	username: one Username,
	password: one Password,
	email: one Email,
	userType: one UserType
} {
	userID > 0
}

sig Username {}
sig Password {}
sig Email {}

sig Farmer extends User {
	performingType: one PerformingType
}

sig Agronomist extends User {
}

sig PolicyMaker extends User {
}

// UserType - enum
abstract sig UserType {}
one sig FARMER extends UserType {}
one sig AGRONOMIST extends UserType {}
one sig POLICY_MAKER extends UserType {}

// PerformingType - enum
abstract sig PerformingType {}
one sig GOOD_PERFORMING extends PerformingType {}
one sig NORMAL_PERFORMING extends PerformingType {}
one sig UNDER_PERFORMING extends PerformingType {}


// Daily Plan
sig DailyPlan {
	day: one Date,
	agronomist: one Agronomist,
	executed: one Bool,
	deviationList: set Farmer,
	visitList: set Visit
}

sig Date {}

sig Visit {
	day: one Date,
	farmer: one Farmer
}

// Bool - enum
abstract sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}


// Message
abstract sig Message {
	messageType: one MessageType,
	sender: one User,
	receiver: set User,
	text: one Text
} {
	// message must have at least one receiver
	#receiver > 0
}

sig Text {}

sig DiscussionMessage extends Message {
}

sig RequestReplyMessage extends Message {
	requestType: one RequestType,
	securityType: one SecurityType,
	requestReplyType: one RequestReplyType
}

// MessageType - enum
abstract sig MessageType {}
one sig REQUEST_REPLY extends MessageType {}
one sig DISCUSSION extends MessageType {}

// RequestType - enum
abstract sig RequestType {}
one sig HELP extends RequestType {}
one sig SUGGESTION extends RequestType {}

// SecurityType - enum
abstract sig SecurityType {}
one sig PUBLIC extends SecurityType {}
one sig PRIVATE extends SecurityType {}

// RequestReplyType
abstract sig RequestReplyType {}
one sig REQUEST extends RequestReplyType {}
one sig REPLY extends RequestReplyType {}


// Forum e Request
sig Forum {
	forumID: one Int,
	dicussionMessageList: set DiscussionMessage
} {
	forumID > 0
}

sig Request {
	requestID: one Int,
	requestReplyMessageList: set RequestReplyMessage
} {
	requestID > 0
}


// Area
sig Area {
	areaID: one Int,
	agronomist: one Agronomist,
	farmers: set Farmer
} {
	areaID > 0
}


//
sig Problem {}
sig Product {}
sig Incentive {}



// FACTS

// userType must be coherent
fact {
	all a: Agronomist | a.userType = AGRONOMIST
	all f: Farmer | f.userType = FARMER
	all pm: PolicyMaker | pm.userType = POLICY_MAKER
}

// different Users have different userIDs
fact {
	no disj u1, u2: User | u1.userID = u2.userID
}

// different Users have different usernames
fact {
	no disj u1, u2: User | u1.username = u2.username
}

// different Users have different emails
fact {
	no disj u1, u2: User | u1.email = u2.email
}

// a password must belong to a User
fact {
	all p: Password | (some u: User | u.password = p)
}

// an email must belong to a User
fact {
	all e: Email | (one u: User | u.email = e)
}

// all daily plans must contain visits with the same date
fact {
	all d: DailyPlan |
		all v: d.visitList | d.day = v.day
}

// unvisitedList must contain only farmers specified in the visitList
fact {
	all d: DailyPlan |
		all f: d.deviationList | (one v: d.visitList | v.farmer.userID = f.userID)
}

// Agronomists are assigned to only one area
fact {
	all ag: Agronomist | 
		one ar: Area | ar.agronomist.userID = ag.userID
}

// User cannot send message to himself
fact {
	all m: Message | m.sender not in m.receiver
}

// Farmers are assigned to only one area
fact {
	all f: Farmer |
		one a: Area | f in a.farmers
}

// unvisitedList can be non-empty only if daily plan has been executed
fact {
	all d: DailyPlan |
		#d.deviationList > 0 implies d.executed = True
}

// PolicyMakers cannot send or receive messages
fact {
	no m: Message | m.sender.userType = POLICY_MAKER

	no m: Message | (some r: m.receiver | r.userType = POLICY_MAKER)
}

// Agronomist cannot send REQUEST messages or DISCUSSION messages
fact {
	no m: RequestReplyMessage | (m.sender.userType = AGRONOMIST and m.requestReplyType = REQUEST)

	no m: DiscussionMessage | m.sender.userType = AGRONOMIST

	no m: DiscussionMessage | (some r: m.receiver | r.userType = AGRONOMIST)
}

// request_reply messages are sent to all agronomists
fact {
	all m: RequestReplyMessage | (all a: Agronomist | a in m.receiver)
}



// ASSERTIONS

assert farmerSendsRequestsAlsoToHisAgronomist {
	all m: RequestReplyMessage | 
		(m.requestType = HELP and m.requestReplyType = REQUEST) implies
			(one a: Area | m.sender in a.farmers and a.agronomist in m.receiver)
}
check farmerSendsRequestsAlsoToHisAgronomist for 5



// PREDICATES

// simulation 1
pred world1 {
	#Farmer = 10
	#Agronomist = 3
	#PolicyMaker = 2
	#DailyPlan = 5
}
run world1 for 20
