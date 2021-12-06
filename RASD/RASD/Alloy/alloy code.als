// User (Farmer, Agronomist, PolicyMaker)
abstract sig User {
	userID: one ID,
	username: one Username,
	password: one Password,
	email: one Email,
	userType: one UserType
}

sig Username {}
sig Password {}
sig Email {}
sig ID {}

sig Farmer extends User {
	performingType: one PerformingType
} {
	userType = FARMER // userType must be coherent
}

sig Agronomist extends User {
} {
	userType = AGRONOMIST // userType must be coherent
}

sig PolicyMaker extends User {
} {
	userType = POLICY_MAKER // userType must be coherent
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
} {
	#visitList > 0
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
	isStartingMessage: one Bool
} {
	messageType = DISCUSSION
}

sig RequestReplyMessage extends Message {
	requestReplyType: one RequestReplyType
} {
	messageType = REQUEST_REPLY
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
	forumID: one ID,
	discussionMessageList: set DiscussionMessage,
	startingUser: one Farmer,
	isSolved: one Bool
}

sig Request {
	requestID: one ID,
	requestReplyMessageList: set RequestReplyMessage,
	requestType: one RequestType,
	participants: set User,
	startingUser: one Farmer,
	isSolved: one Bool
}

// Area
sig Area {
	areaID: one ID,
	agronomist: one Agronomist,
	farmers: set Farmer
}


//
sig Problem {}
sig Product {}
sig Incentive {}



// FACTS

// credentials constraints
fact {
	// different Users have different userIDs
	no disj u1, u2: User | u1.userID = u2.userID

	// different Users have different usernames
	no disj u1, u2: User | u1.username = u2.username

	// different Users have different emails
	no disj u1, u2: User | u1.email = u2.email

	// a password must belong to a User
	all p: Password | (some u: User | u.password = p)

	// an email must belong to a User
	all e: Email | (one u: User | u.email = e)
}

// Daily Plan constraints
fact {
	// all daily plans must contain visits with the same date
	all d: DailyPlan |
		all v: d.visitList | d.day = v.day

	// unvisitedList must contain only farmers specified in the visitList
	all d: DailyPlan |
		all f: d.deviationList | (one v: d.visitList | v.farmer.userID = f.userID)

	// unvisitedList can be non-empty only if daily plan has been executed
	all d: DailyPlan |
		#d.deviationList > 0 implies d.executed = True

	// different daily plans must have different dates
	no disj d1, d2: DailyPlan | d1.day = d2.day

	// a daily plan cannot contain multiple visits to the same farmer
	all d: DailyPlan |
		no disj v1, v2: d.visitList | v1.farmer.userID = v2.farmer.userID

	// a visit must belong to a daily plan
	all v: Visit |
		one d: DailyPlan | v in d.visitList
}

// Agronomists are assigned to only one area
fact {
	all ag: Agronomist | 
		one ar: Area | ar.agronomist.userID = ag.userID
}

// Farmers are assigned to only one area
fact {
	all f: Farmer |
		one a: Area | f in a.farmers
}

// Messages constraints
fact {
	// User cannot send messages to himself
	all m: Message | m.sender not in m.receiver

	// PolicyMakers cannot send or receive messages and participate to Requests
	no m: Message | m.sender.userType = POLICY_MAKER
	no m: Message | (some r: m.receiver | r.userType = POLICY_MAKER)
	no r: Request | (some p: r.participants | p.userType = POLICY_MAKER)

	// Agronomist cannot send REQUEST messages or DISCUSSION messages
	no m: RequestReplyMessage | (m.sender.userType = AGRONOMIST and m.requestReplyType = REQUEST)
	//all m: RequestReplyMessage | (m.sender.userType = AGRONOMIST implies m.requestReplyType = REPLY)
	no m: DiscussionMessage | m.sender.userType = AGRONOMIST
	no m: DiscussionMessage | (some r: m.receiver | r.userType = AGRONOMIST)

	// discussion messages must belong to a Forum
	all m: DiscussionMessage |
		one f: Forum | m in f.discussionMessageList

	// request_reply message must belong to a Request
	all m: RequestReplyMessage |
		one r: Request | m in r.requestReplyMessageList

	/*
	// request_reply messages sent by farmers are delivered to all agronomists
	all m: RequestReplyMessage |
		(m.sender.userType = FARMER implies (all a: Agronomist | a in m.receiver))

	// request_reply messages sent by agronomists are delivered to all other agronomists (but not to himself) and to farmers
	all m: RequestReplyMessage | 
		(m.sender.userType = AGRONOMIST implies
			(one a: Agronomist | 
				(m.sender = a and (a not in m.receiver) and (all a2: Agronomist | a2 != a implies a2 in m.receiver))
			)
		)
	
	// for farmers, private request_reply messages sent by agronomists are delivered only to the farmer that started the conversation
	all r: Request |
		r.securityType = PRIVATE implies
			(all m: r.requestReplyMessageList | 
				(m.sender.userType = AGRONOMIST implies (r.startingUser in m.receiver)))

	// private request conversation constraints:
	// the receiver can be an agronomist or the farmer that started the conversation
	// the only farmer that can send messages is the one that started the conversation
	all r: Request |
		r.securityType = PRIVATE implies
			(all m: r.requestReplyMessageList |
				((all u: m.receiver | (u.userType = AGRONOMIST or u = r.startingUser))
				and (m.sender.userType = FARMER implies m.sender = r.startingUser))
			)
	*/
}

// Requests constraints
fact {
	// requests from a farmer must have as participant the Agronomist responsible of the farmer's area
	all r: Request | one a: Area | (r.startingUser in a.farmers and a.agronomist in r.participants)

	// requests must have as participant the farmer that started it
	all r: Request | r.startingUser in r.participants

	// request messages must be delivered to all the participants, but not to the sender
	all r: Request | 
		all m: r.requestReplyMessageList |
			all p: r.participants | (p in m.receiver or p = m.sender)

	// request messages must be sent by and delivered to participants only
	all r: Request |	
		all m: r.requestReplyMessageList |
			(all u: m.receiver | u in r.participants) and m.sender in r.participants

	// a request message must be sent by the farmer who started the conversation
	all r: Request |
		all m: r.requestReplyMessageList | (m.requestReplyType = REQUEST implies (m.sender = r.startingUser and m.sender.userType = FARMER))	

	// a request discussion must contain only one request message
	all r: Request |
		one m: r.requestReplyMessageList | m.requestReplyType = REQUEST
}

// Forum constraints
fact {
	// forum messages must be delivered to all farmers, but not to the sender
	all m: DiscussionMessage |
		all f: Farmer | (f in m.receiver or f = m.sender)

	// forums can have only one starting message
	all f: Forum |
		one m: f.discussionMessageList | m.isStartingMessage = True

	// starting message must belong to starting user
	all f: Forum |
		all m: f.discussionMessageList | 
			m.isStartingMessage = True implies m.sender = f.startingUser
}



// ASSERTIONS

assert agronomistRepliesToARequest {
	no m: RequestReplyMessage | 
		m.sender.userType = AGRONOMIST
}
//check agronomistRepliesToARequest for 20

assert multipleFarmersCanWriteInAForum {
	no f: Forum |
		some m: f.discussionMessageList | m.sender != f.startingUser 
}
//check multipleFarmersCanWriteInAForum for 20



// PREDICATES

// simulation 1 - Daily Plan and Visit
pred world1 {
	#Farmer = 3
	#Agronomist = 1
	#PolicyMaker = 0
	#DailyPlan = 2
	#Message = 0
	#Visit = 5
}
//run world1 for 20

// simulation 2 - Request
pred world2 {
	#Farmer = 3
	#Agronomist = 2
	#PolicyMaker = 0
	#DailyPlan = 0
	#DiscussionMessage = 0
	#Request = 1
	#Request.participants = 4
	#RequestReplyMessage = 3
}
//run world2 for 20

// simulation 3 - Forum
pred world3 {
	#Farmer = 4
	#Agronomist = 1
	#PolicyMaker = 0
	#DailyPlan = 0
	#DiscussionMessage = 4
	#Request = 0
}
//run world3 for 20

// simulation 4 - Policy Maker
pred world4 {
	#Farmer = 3
	#Agronomist = 2
	#PolicyMaker = 4
}
run world4 for 10
