open util/boolean

//First, all the entities necessary to describe the objects from the class diagram
sig Username{}

sig Password{}

sig Date{}

sig Bitmap{}

sig LicensePlate{}

//----------------------------------------------------------------------//
//Now, the description of the objects from the class diagram

//For the position, the values of latitude and longitude are scaled
//Latitude >= -90 and Latitude <= 90
//Longitude >= -180 and Longitude <= 180
sig Position{
	latitude: one Int,
	longitude: one Int
}
{latitude >= -3 and latitude <= 3 and longitude >= -6 and longitude <= 6}

sig Registration{
	username: one Username,
	password: one Password
}

abstract sig Customer{
	registration: one Registration
}

sig User extends Customer{
	pictures: set Picture,
	violationsSent: set Violation,
	streetsMap: set Street
}

sig Authority extends Customer{
	allViolations: set Violation,
	streetsMap: set Street
}

sig Municipality extends Customer{
	trafficTickets: set TrafficTicket,
	interventions: set Intervention,
	accidents: set Accident,
	allViolations: set Violation,
	warningsReceived: set Warning
}

sig Picture{
	date: one Date,
	image: one Bitmap,
	position: one Position
}

//In each recognition, it's needed to the picture be related to the violation
sig Recognition{
	picture: one Picture,
	violation: lone Violation
}
{picture in violation.pictures}

sig Violation{
	licencePlate: one LicensePlate,
	street: one Street,
	pictures: some Picture,
	violationDate: one Date
}

sig Street{
	safe: one Bool,
	accidentsStreet: set Accident
}
{safe = False iff #accidentsStreet > 0}

sig Accident{
	accidentDate: one Date
}

sig Intervention{
	targetMunicipality: one Municipality
}

sig TrafficTicket{
	licensePlateTrafficTicket: one LicensePlate,
	dateEmission: one Date
}

sig Statistic{
	data: set TrafficTicket
}

//----------------------------------------------------------------------//
//Errors handling

abstract sig Request{}
abstract sig Warning{}

sig Data{}

one sig TransferWarning extends Warning{}
one sig SystemWarning extends Warning{}

sig SingleRequest{
	authorOfRequest: one Municipality,
	subjectOfRequest: one Data
}

abstract sig SingleRequestResult{
	request: set SingleRequest
}

one sig SingleRequestAccepted extends SingleRequestResult{}
one sig SingleRequestRefused extends SingleRequestResult{}

//Transfer request generates a warning if the data is not fully sent
//The values were scaled for simplicity
sig TransferRequest{
	transferData: set Data,
	authorOfRequestTransfer: one Municipality,
	transferWarning: lone TransferWarning
}
{#transferWarning = 1 iff #transferData < 10}

//System request generates a warning if the system is not ready
//The values were scaled for simplicity
sig SystemRequest{
	ready: one Bool,
	authorOfRequestSystem: one Municipality,
	systemWarning: lone SystemWarning
}
{#systemWarning = 1 iff ready = False}

//----------------------------------------------------------------------//

//All usernames have to be associated to a Registration
fact UsernameRegistrationConnection{
	all u: Username | some r: Registration | u in r.username
}

//All passwords have to be associated to a Registration
fact PasswordRegistrationConnection{
	all p: Password | some r: Registration | p in r.password
}

//All customers have to be associated to a Registration
fact RegistrationCostumerConnection{
	all r: Registration | some c: Customer | r in c.registration
}

//Every customer has a unique username
fact UniqueUsername{
	no disj c1, c2: Customer | c1.registration.username = c2.registration.username
}

//The municipality has made a request that has not been accepted if it
//has been notified with the warning
fact TransferWarningOnlyIfNeeded{
	all m: Municipality | TransferWarning in m.warningsReceived implies
	(
		some sr: SingleRequest | m in sr.authorOfRequest and
		(one r: SingleRequestRefused | sr in r.request)
	)
}

fact SystemWarningOnlyIfNeeded{
	all m: Municipality | SystemWarning in m.warningsReceived implies
	(
		some sr: SingleRequest | m in sr.authorOfRequest and
		(one r: SingleRequestRefused | sr in r.request)
	)
}

//The municipality is notified when a transfer is not concluded
fact TransferWarningIfFailed{
	all sr: SingleRequest | one r: SingleRequestRefused | sr in r.request
	implies
	(
		TransferWarning in sr.authorOfRequest.warningsReceived
	)
}

//The municipality is notified when the system is not ready
fact SystemWarningIfFailed{
	all sr: SingleRequest | one r: SingleRequestRefused | sr in r.request
	implies
	(
		SystemWarning in sr.authorOfRequest.warningsReceived
	)
}

//The municipality is notified if had transfer problems
fact NotFullyTransfered{
	all tr: TransferRequest | #tr.transferData < 10
	implies
	(
		TransferWarning in tr.authorOfRequestTransfer.warningsReceived
	)
}

//The municipality is notified if had system problems
fact NotSystemAvailable{
	all sr: SystemRequest | sr.ready = False
	implies
	(
		SystemWarning in sr.authorOfRequestSystem.warningsReceived
	)
}

//Every single request can be either accepted or refused, not both
fact SingleRequestAcceptedOrRefused{
	all sr: SingleRequest | (some srr: SingleRequestResult | sr in srr.request)
	and (no disj srr1, srr2: SingleRequestResult | sr in srr1.request and sr in srr2.request)
}

//Every picture has an author
fact PictureUserConnection{
	all p: Picture | some u: User | p in u.pictures
}

//There are no two different violations with the same license plate and the same date
fact DateViolationConnection{
	no disj v1, v2: Violation | v1.licencePlate = v2.licencePlate and v1.violationDate = v2.violationDate
}

//All positions have to be associated to a Picture
fact PositionPictureConnection{
	all pos: Position | some p: Picture | pos = p.position
}

//All accidents have to be associated to a Street
fact AccidentStreetConnection{
	all acc: Accident | some s: Street | acc in s.accidentsStreet
}

//All accidents have to belong to a municipality
fact AccidentMunicipalityConnection{
	all acc: Accident | some m: Municipality | acc in m.accidents
}

//All the inverventions have to belong to a municipality
fact InterventionMunicipalityConnection{
	all i: Intervention | some m: Municipality | i in m.interventions
}

//If there are no accidents, there are no interventions
fact NoAccidentsNoInterventions{
	
}

//All the traffic tickets have to belong to a municipality
fact TrafficTicketMunicipalityConnection{
	all tt: TrafficTicket | some m: Municipality | tt in m.trafficTickets
}

//Every bitmap belongs to a picture
fact BitMapPictureConnection{
	all bm: Bitmap | some p: Picture | bm = p.image
}

//Every license plate belongs to a violation
fact LicensePlateViolationConnection{
	all lp: LicensePlate | some v: Violation | lp = v.licencePlate
}

//Every traffic ticket belongs to a license plate
fact TrafficTicketLicensePlateConnection{
	all tt: TrafficTicket | some lp: LicensePlate | lp = tt.licensePlateTrafficTicket
}

//Every date needs to be related to a picture or to an accident or to a traffic ticket
fact DateConnection{
	all d: Date | (some p: Picture | d in p.date)
	or
	(some acc: Accident | d = acc.accidentDate)
	or
	(some tt: TrafficTicket | d = tt.dateEmission)
}

//----------------------------------------------------------------------//
//Testing

assert TransferRequestHasWarningCorrectly{
	all tr: TransferRequest | #tr.transferData = 10 iff #tr.transferWarning = 0
}

assert SystemRequestHasWarningCorrectly{
	all sr: SystemRequest | sr.ready = True iff #sr.systemWarning = 0
}

assert NoSingleRequestBothAcceptedAndRefused{
	no sr: SingleRequest | (one a: SingleRequestAccepted | sr in a.request)
	and (one r: SingleRequestRefused | sr in r.request)
}

check TransferRequestHasWarningCorrectly for 5

check SystemRequestHasWarningCorrectly for 5

check NoSingleRequestBothAcceptedAndRefused for 5

//----------------------------------------------------------------------//
//Predicates to generate worlds
//World 1: test requests from municipality
pred world1{
	#SingleRequest = 2
	#SingleRequestAccepted.request = 1
	#SingleRequestRefused.request = 1
	#Municipality = 2
	(some disj m1, m2: Municipality | some disj s1, s2: SingleRequest |
	m1 in s1.authorOfRequest and m2 in s2.authorOfRequest and
	s1 in SingleRequestAccepted.request and s2 in SingleRequestRefused.request)
}

run world1 for 3 but 0 Intervention, 0 Street, 0 TrafficTicket, 0 Statistic

//World 2: test transfer request
pred world2{
	#TransferRequest = 1
	#Municipality = 1
	(some t1: TransferRequest | #t1.transferData = 3)
}

run world2 for 3 but 0 Intervention, 0 Street, 0 TrafficTicket, 0 Statistic

//World 3: test system request
pred world3{
	#SystemRequest = 2
	#SingleRequestAccepted.request = 1
	#SingleRequestRefused.request = 1
	#Municipality = 2
	(some disj s1, s2: SystemRequest | s1.authorOfRequestSystem != s2.authorOfRequestSystem
	and s1.ready = False and s2.ready = True)
}

run world3 for 3 but 0 Intervention, 0 Street, 0 TrafficTicket, 0 Statistic

//World 4: everything
pred world4{
	#Violation = 2
}

run world4 for 2 but 0 SingleRequest, 0 TransferRequest, 0 SystemRequest