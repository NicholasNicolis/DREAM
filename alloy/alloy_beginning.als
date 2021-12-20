//Represents a set of farm
sig Zone{
	farms: some Farm,
}
//Represents the policy maker
sig PolicyMaker{
	areas: one Zone,
}
//Represents the farmer
sig Farmer{
	farm: some Farm,
}
//Represent the farm 
sig Farm{
weather: set Weather
//Weather = 7 in order to represents the 7 days of the week
}{#weather = 7}

//Represents the weather of one day of the week
sig Weather{

}
//Represents the archive linked with all the farmers
sig Archive{	
	//every Forum has a set of Farmer
	farmers: some Farmer
}

sig Report{
	//There is a report for every farm owned by a farmer
	farms: one Farm,
	//a report obtained bya PolicyMaker
	pms: one PolicyMaker
}
//The forum is unique and can be seen by everyone
sig Forum{
	//a Forum has a set of PolicyMaker
	pms:some PolicyMaker,
	//a Forum has a set of Farmer
	farmers: some Farmer
}

//Multiple tickets can be sent by farmers to the respective policy makers
sig Ticket{
	//a report compiled bya farmer 
	farmers: some Farmer,
	//a report obtained bya PolicyMaker
	pms: lone PolicyMaker
}

//The ticket must be sent to a policy maker who is responsible for the area where the farmer has his/her farm
pred sameTicketFarmerPm[pm: PolicyMaker ,far:Farmer,ti:Ticket] {
	pm in ti.pms and far in ti.farmers 
}
fact "same ticket per pm and farmer"{
	all pm:PolicyMaker, f:Farmer, ti:Ticket | sameTicketFarmerPm[pm,f,ti] implies f.farm = pm.areas.farms
}


//The report must be sent to a policy maker who is responsible for the area where the farmer has his/her farm
pred sameReportFarmerPm[pm: PolicyMaker ,far:Farm,re:Report] {
	pm in re.pms and far in re.farms
}
fact "same Report per pm and farmer"{
	all pm:PolicyMaker, f:Farm, re:Report | sameReportFarmerPm[pm,f,re] implies f = pm.areas.farms
}

//For semplicity we assume that a policy maker can receive one report for each farm
fact "one PolicyMaker Per Report"{
	all pm: PolicyMaker | one r:Report | pm in r.pms
}

//Every farm is assigned to a report which will be sent to the respective policy maker
fact "one report per farm"{
	all far: Farm| one r:Report| far in r.farms
}

//Every farm is associated with 7 weather signature to indicate the 7 days of the week
fact "7 weathers per farm"{
	all w:Weather | one f:Farm | w in f.weather
}

//A farm can be owned by only one farmer
fact "one farmer per farm"{
	all farms:Farm | one f: Farmer | farms in f.farm 
}

//We assume that there aren't intersection between areas
fact "no 2 area for the same farm"{
	all farm:Farm | one a: Zone | farm in a.farms 
}

//Every area is associated with one policy maker
fact "one pm per area"{
	all area:Zone | one pm: PolicyMaker | area in pm.areas 
}

//The forum is unique for every policy maker
fact "one forum per pm"{
	all pm: PolicyMaker | one f:Forum| pm in f.pms
}

//The forum is unique for every farmer
fact "one forum per farmer"{
	all far: Farmer| one f:Forum| far in f.farmers
}

//The archieve is unique for every farmer
fact "one Archive per farmer"{
	all far: Farmer| one a:Archive| far in a.farmers
}


pred show{
	#Forum = 1
	#Archive = 1
	#Farmer = 3
}

run show for 40



