// User (Farmer, Agronomist, PolicyMaker)
abstract sig User {
	userID: one ID,
	username: one Username,
	password: one Password,
	email: one Email
}

sig Username {}
sig Password {}
sig Email {}
sig ID {}

sig Farmer extends User {
	performingType: one PerformingType
}

sig Agronomist extends User {
	specialization: one SpecializationType
}

sig PolicyMaker extends User {}


// PerformingType - enum
abstract sig PerformingType {}
one sig GOOD_PERFORMING extends PerformingType {}
one sig NORMAL_PERFORMING extends PerformingType {}
one sig UNDER_PERFORMING extends PerformingType {}

// SpecializationType - enum
abstract sig SpecializationType {}
one sig SPECIALIZATION_A extends SpecializationType {}
one sig SPECIALIZATION_B extends SpecializationType {}
one sig SPECIALIZATION_C extends SpecializationType {}


// Daily Plan
sig DailyPlan {
	date: one Date,
	agronomist: one Agronomist,
	executed: one Bool,
	deviationList: set Farmer,
	visitList: set Visit
} {
	#visitList > 0
}

sig Date {}

sig Visit {
	date: one Date,
	farmer: one Farmer
}

// Bool - enum
abstract sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}


// Message
abstract sig Message {
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
}

sig ChatMessage extends Message {
	isRequestMessage: one Bool
}


// RequestType - enum
abstract sig RequestType {}
one sig HELP extends RequestType {}
one sig SUGGESTION extends RequestType {}


// Forum e Request
sig Forum {
	forumID: one ID,
	discussionMessageList: set DiscussionMessage,
	startingUser: one Farmer,
	isSolved: one Bool
}

sig RequestChat{
	requestID: one ID,
	title: one ChatTitle,
	chatMessageList: set ChatMessage,
	requestType: one RequestType,
	participants: set User,
	startingUser: one Farmer
}

sig ChatTitle {}


// Area
sig Area {
	areaID: one ID,
	agronomists: set Agronomist,
	farmers: set Farmer
} {
	// non-empty area
	#agronomists > 0
	#farmers > 0
}


//
sig Problem {}

// ProductType - enum
abstract sig ProductType {}
one sig PRODUCT_A extends ProductType {}
one sig PRODUCT_B extends ProductType {}
one sig PRODUCT_C extends ProductType {}

sig Amount {}
sig UnitOfMeasurement {}


sig Product {
	type: one ProductType,
	amount: one Amount,
	unitOfMeasurement: one UnitOfMeasurement,
	--description: one String	
}


// Incentive
sig Incentive {
	incentiveID: one ID,
	--description: one String,
	value: one Amount
}

sig IncentiveAssigning{
	incentive: one Incentive,
	incentiveGiver: one PolicyMaker,
	receiver: one Farmer,
	date: one Date
}


// Good Practice
sig GoodPractice {
	practiceID: one ID,
	requestedBy: one PolicyMaker,
	requestedTo: one Farmer,
	content: one Text
}



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
		all v: d.visitList | d.date = v.date

	// unvisitedList must contain only farmers specified in the visitList
	all d: DailyPlan |
		all f: d.deviationList | (one v: d.visitList | v.farmer.userID = f.userID)

	// unvisitedList can be non-empty only if daily plan has been executed
	all d: DailyPlan |
		#d.deviationList > 0 implies d.executed = True

	// different daily plans must have different dates
	no disj d1, d2: DailyPlan | d1.date = d2.date

	// a daily plan cannot contain multiple visits to the same farmer
	all d: DailyPlan |
		no disj v1, v2: d.visitList | v1.farmer.userID = v2.farmer.userID

	// a visit must belong to a daily plan
	all v: Visit |
		one d: DailyPlan | v in d.visitList
}

// Agronomists are assigned to at least one area
fact {
	all ag: Agronomist | 
		some ar: Area | ag in ar.agronomists
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

	// PolicyMakers cannot send messages
	no m: Message | m. sender in PolicyMaker

	// PolicyMakers cannot receive messages
	no m: Message | (some r: m.receiver | r in PolicyMaker)

	// PolicyMakers cannot participate to requests
	no r: RequestChat | (some p: r.participants | p in PolicyMaker)

	// Agronomist cannot send REQUEST messages or DISCUSSION messages
	no m: ChatMessage | (m.sender in Agronomist and m.isRequestMessage = True)

	// all m: RequestReplyMessage | (m.sender.userType = AGRONOMIST implies m.requestReplyType = REPLY)
	no m: DiscussionMessage | m.sender in Agronomist
	no m: DiscussionMessage | (some r: m.receiver | r in Agronomist)

	// discussion messages must belong to a Forum
	all m: DiscussionMessage |
		one f: Forum | m in f.discussionMessageList

	// request_reply message must belong to a Request
	all m: ChatMessage |
		one r: RequestChat | m in r.chatMessageList
}

// Requests constraints
fact {
	/* requests from a farmer must have as participant at least one Agronomist
	responsible of the farmer's area*/
	all r: RequestChat | one a: Area | 
		(r.startingUser in a.farmers and 
		(some ag: a.agronomists | ag in r.participants))

	// requests must have as participant the farmer that started it
	all r: RequestChat | r.startingUser in r.participants

	// request messages must be delivered to all the participants, but not to the sender
	all r: RequestChat | 
		all m: r.chatMessageList |
			all p: r.participants | (p in m.receiver or p = m.sender)

	// request messages must be sent by and delivered to participants only
	all r: RequestChat |	
		all m: r.chatMessageList |
			(all u: m.receiver | u in r.participants) and m.sender in r.participants

	// a request message must be sent by the farmer who started the conversation
	all r: RequestChat |
		all m: r.chatMessageList | (m.isRequestMessage = True
			implies (m.sender = r.startingUser and m.sender in Farmer))	


	// a request discussion must contain only one request message
	all r: RequestChat |
		one m: r.chatMessageList | m.isRequestMessage = True
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

// Incentive constraints
fact {
	// no incentive assigned multiple times on the same date to the same farmer
	no disj ia1, ia2: IncentiveAssigning | 
		ia1.incentive = ia2.incentive and ia1.receiver = ia2.receiver and ia1.date = ia2.date

	// different incentives have different IDs
	no disj i1, i2: Incentive | i1.incentiveID = i2.incentiveID
}

// Good Practice constraints
fact {
	// different good practices have different IDs
	no disj gp1, gp2: GoodPractice | gp1.practiceID = gp2.practiceID
}

// an ID is assigned to only one entity
fact {
	no f: Forum, rc: RequestChat | f.forumID = rc.requestID
	no f: Forum, u: User | f.forumID = u.userID
	no rc: RequestChat, u: User | rc.requestID = u.userID
	no i: Incentive, rc: RequestChat | i.incentiveID = rc.requestID
	no i: Incentive, f: Forum | i.incentiveID = f.forumID
	no i: Incentive, u: User | i.incentiveID = u.userID
	no gp: GoodPractice, f: Forum | gp.practiceID = f.forumID
	no gp: GoodPractice, rc: RequestChat | gp.practiceID = rc.requestID
	no gp: GoodPractice, u: User | gp.practiceID = u.userID
	no gp: GoodPractice, i: Incentive | gp.practiceID = i.incentiveID
	no a: Area, f: Forum | a.areaID = f.forumID
	no a: Area, rc: RequestChat| a.areaID = rc.requestID
	no a: Area, u: User | a.areaID = u.userID
	no a: Area, i: Incentive | a.areaID = i.incentiveID
	no a: Area, gp: GoodPractice | a.areaID = gp.practiceID
}



// ASSERTIONS

// farmers are supervised by at least one agronomist
assert farmersAreSupervisedByAtLeastOneAgronomist {
	all f: Farmer | one a: Area | 
		some ag: Agronomist | f in a.farmers and ag in a.agronomists
}
check farmersAreSupervisedByAtLeastOneAgronomist for 20

// farmers can send requests for help to agronomists
assert farmersCanSendRequestsForHelpToAgronomists {
	all r: RequestChat| 
		some f: Farmer |
			some ag: Agronomist | f in r.participants and ag in r.participants
}
check farmersCanSendRequestsForHelpToAgronomists for 20

// farmers can receive visits from agronomists
assert farmersCanReceiveVisitsFromAgronomists {
	all d: DailyPlan |
		some v: Visit |
			v in d.visitList
}
check farmersCanReceiveVisitsFromAgronomists for 20

// policy makers can assign incentives to farmers
assert policyMakerCanAssignIncentivesToFarmers {
	all i: IncentiveAssigning | i.incentive in Incentive and i.incentiveGiver in PolicyMaker and i.receiver in Farmer
}
check policyMakerCanAssignIncentivesToFarmers for 20



// PREDICATES

// simulation 1 - Daily Plan and Visit
pred world1 {
	#Farmer = 3
	#Agronomist = 1
	#PolicyMaker = 0
	#DailyPlan = 2
	#Message = 0
	#Visit = 4
}
run world1 for 20

// simulation 2 - Request
pred world2 {
	#Farmer = 3
	#Agronomist = 2
	#PolicyMaker = 0
	#DailyPlan = 0
	#DiscussionMessage = 0
	#RequestChat = 1
	#RequestChat.participants = 4
	#ChatMessage = 3
}
run world2 for 20

// simulation 3 - Forum
pred world3 {
	#Farmer = 4
	#Agronomist = 1
	#PolicyMaker = 0
	#DailyPlan = 0
	#DiscussionMessage = 4
	#RequestChat = 0
	#Product = 0
	#Incentive = 0
}
run world3 for 20

// simulation 4 - Good Practice
pred world4 {
	#Farmer = 2
	#Agronomist = 1
	#PolicyMaker = 2
	#GoodPractice = 3
}
run world4 for 10

// simulation 5 - Incentive
pred world5 {
	#Farmer = 2
	#PolicyMaker = 4
	#IncentiveAssigning = 2
	# Incentive = 3
	# Product = 0
	#DailyPlan = 0
	#Message = 0
}
run world5 for 10
