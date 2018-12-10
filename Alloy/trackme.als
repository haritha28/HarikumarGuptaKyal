sig Individual  {
age : one Int,
device: wearableDevice,
ath: set Athlete,
sp: set Spectator,
critical: one Critical
}
{age> 0
critical= True}

sig Thirdparty{
groupReq: one GroupRequests,
indReq: one  IndRequests,
org: set  Organizer,
sp: set Spectator
}

sig wearableDevice{
location: one Location,
health: one Health
}

sig Location{
latitude: Int,
longitude: Int
}

sig Health{
heartbeat: Int, 
steps: Int,
otherVitals: Int
}

sig GroupRequests{
noofRequest: one Int,
noofInd: one Int
}
{noofRequest>0
noofInd>0}

sig IndRequests{
noofRequest: one Int
}
{noofRequest>0}

one sig Athlete{
event : one Event
}

one sig Organizer{
event : one Event
}

one sig Spectator{
event : one Event
}

sig Event{
id :  one Int,
date: one Date,
time: one Time,
path: one Location
}
{id=1
#time=1}

sig Ambulance{
ambno: one String,
ambloc: one State,
indloc: one Location,
indhealth: one Health
}
{ambloc = near}

abstract sig State{}
one sig near extends State{}
one sig far extends State{}

sig Time{}
sig Date{}

abstract sig Critical{}
one sig True extends Critical{}
one sig False extends Critical{}

--Every Individual has one wearable Device
fact sameValuesperDevice{
no disjoint w,w':wearableDevice | (w.location=w'.location and w.health=w'.health)
}

--ALl requests are linked to thirdparty
fact RequestsLinkedToThirdParty{
all t:Thirdparty, g:GroupRequests, ir: IndRequests | (t.groupReq=g and t.indReq=ir)
}

--All Organizer are Third Party
fact OrganizerThirdparty{
all t: Thirdparty, o: Organizer | t.org=o
}

--All Ahlete are  Individual
fact AthleteIndividual{
all i: Individual, a: Athlete | i.ath=a
}

--All Spectator are either Individual or Third party
fact SpectatorIndividualORThirdParty{
some i: Individual, t: Thirdparty, s: Spectator | (i.sp = s or t.sp =s)
}

--Organizers, Athlete and Spectator are related to event at a time.
fact sameEvent{
no disjoint e,e': Event, a: Athlete, o: Organizer, s:Spectator |  (a.event=e and o.event=e and s.event=e) and 
(a.event=e' and o.event=e' and s.event=e')
}

--Every Location and health is linked to wearable device
fact ValuesperDevice {
all w:wearableDevice, l:Location, h:Health | (w.location=l and w.health=h)
}

--Ambulance connected to Individual's health and location with critical condition is true
fact AmbulanceGettingDetails{
one i: Individual, a: Ambulance | ((i.critical=True and a.ambloc=near) implies ( a.indhealth = i.device.health  and a .indloc = i.device.location))
}

--Every location and health maps to same device
assert DetailsPerWearableDevice {
all i: Individual, d: i.device, w:wearableDevice | d = w
}

--An oragnizer defines the path of the event which the athlete joins and is watched by spectator
assert OneEventPerAthleteAndOrganizer{
all e:Event, a: Athlete, o: Organizer, s:Spectator | (a.event=e and o.event=e and s.event=e)
}

pred show{
(one i: Individual | #i.device=1) and 
(one t:Thirdparty | #t.groupReq=1) and 
(one a:Ambulance | a.ambno="MI8754")
}

run show

check OneEventPerAthleteAndOrganizer for 1

check DetailsPerWearableDevice for 1



run show
