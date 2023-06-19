/* 
 * Automatic GreenHouse
 *  ...
 *  
 */

/* PROPERTIES */

ltl exp  { [] !(has_expired) } // the system harvests at most LIMIT_EXPIRED expired plants
ltl temp { [] temp_in_bounds } // the average temperature never gets below FREEZING_TEMP or above BURNING_TEMP
ltl rate { [] rate_expired }   // the system keeps a rate of 1 (or less) expired plant every RATE_EXPIRED mature plants harvested

ltl timed_exp  { [] !(timed_expired) } // same as 'exp' but only for the first TIME_LIMIT time steps
ltl timed_temp { [] timed_temp }       // same as 'temp' but only for the first TIME_LIMIT time steps
ltl timed_rate { [] timed_rate }       // same as 'rate' but only for the first TIME_LIMIT time steps


/* MACROS */

#define N_PLANT_BEDS 5        // number of plant beds
#define N_HARVESTERS 2    // number of harvester robots
#define N_SEEDERS 2       // number of robots that plant seeds

#define RANDOM_START false // starting age for plant beds is randomized between [AGE_NO_PLANT, AGE_MATURE]

#define COLD_PREEMPTIVE 2 // the heater will be turned ON when temp is this close to safe limits
#define HOT_PREEMPTIVE (TEMP_INCREASE)  // the heater will be turned OFF when ...

#define LIMIT_EXPIRED 0   // How many expired plants the system tolerates
#define RATE_EXPIRED 10   // Tolerates 1 expired plant every RATE_EXPIRED mature harvested plants
#define TIME_LIMIT   50   // for how many steps we want the system to satisfy the properties

// Monitor, heat manager, global weather, plants, harvesters, and seeders.
#define N_PROCESSES (1 + 1 + 1 + N_PLANT_BEDS + N_HARVESTERS + N_SEEDERS)

#define FREEZING_TEMP 0   // plant freezes to death
#define MIN_SAFE_TEMP 5   // min temperature for the plants
#define MAX_SAFE_TEMP 10  // max temperature for the plants
#define BURNING_TEMP  15  // plant combust into flames
#define START_TEMP ((MIN_SAFE_TEMP+MAX_SAFE_TEMP)/2 ) // starting greenhouse temperature
#define TEMP_INCREASE 3   // when heater is ON

#define AGE_NO_PLANT 0    // when the plant bed has no plant
#define AGE_PLANTED 1     // starting age for the plant
#define AGE_MATURE 5      // from this age age the plant can be harvested
#define AGE_EXPIRED 10    // from this age the plant can no longer be harvested

#define COLD_RATE 0       // growth rate with cold temperatures
#define SAFE_RATE 1       // growth rate with safe temperatures
#define HOT_RATE 2        // growth rate with hot temperatures

#define WEATHER_MIN_LEN 3     // minimum number of time steps of a weather period
#define WEATHER_MAX_LEN 5     // maximum number of time steps of a weather period
#define WEATHER_MIN_RATE (-4) // maximum temperature decrease
#define WEATHER_MAX_RATE 0    // maximum temperature increase

#define CHANNEL_LEN (N_HARVESTERS + N_SEEDERS) // length of the FIFO channels
#define MY_PLANTS_LEN ((N_PLANT_BEDS/N_SEEDERS)+(N_PLANT_BEDS%N_SEEDERS)) // upper-bound on how many plants can be assigned to a process


/* TYPES */

mtype = { TIME, HARVEST, SEED };
typedef sensor_read {
	byte age;
	short temp;
}

/* GLOBAL VARIABLES */

short       weather_temp_rate = 0;      // influence of the global weather to the temp of each plant
bool        heaters[N_PLANT_BEDS];          // if the plant is actively receiving heat
sensor_read plant_sensors[N_PLANT_BEDS];    // readings from the sensors of every plant
byte        plant_harvesters[N_PLANT_BEDS]; // which harvester can harvest which plant bed
byte        plant_seeders[N_PLANT_BEDS];    // which seeder can seed which plant bed
byte        n_mature_harvested = 0;     // number of mature plants harvested
byte        n_expired_harvested = 0;    // number of expired plants
byte        n_planted = 0;
bool        has_expired = false;        // for the monitor
bool        temp_in_bounds = true;      // for the monitor
bool        rate_expired = true;        // for the monitor
int         time_step = 0;              // for the monitor, updated by global_clock
bool        timed_expired = false;
bool        timed_temp = false;
bool        timed_rate = false;

/* CHANNELS */
chan clock[N_PROCESSES] = [0] of { mtype };
chan plant_action[N_PLANT_BEDS] = [CHANNEL_LEN] of { mtype };


/* UTILITY */

/**
 * Randomly chooses a number between min and max (inclusive).
 */
inline get_random(n, min, max)
{
	n = min;
	do
	:: (n < max) -> n++;
	:: break;
	od;
}

/**
 * Decides the growth rate of the plant given the current temperature.
 */
inline get_growth_rate(rate, temp)
{
	if
	:: (temp <= FREEZING_TEMP) ->
			rate = AGE_EXPIRED;
	:: ((temp > FREEZING_TEMP) && (temp < MIN_SAFE_TEMP)) ->
			rate = COLD_RATE;
	:: ((temp >= MIN_SAFE_TEMP) && (temp <= MAX_SAFE_TEMP)) ->
			rate = SAFE_RATE;
	:: ((temp > MAX_SAFE_TEMP) && (temp < BURNING_TEMP)) ->
			rate = HOT_RATE;
	:: (temp >= BURNING_TEMP) -> rate = AGE_EXPIRED;
	:: else -> assert(false); // something bad happened
	fi;
}


/* PROCESSES */

proctype monitor(byte my_id)
{
	assert(RATE_EXPIRED > 0);
	int avg_temp;
	byte i;
	do
	:: atomic { 
		clock[my_id] ? _;
		
// check_expired:
		if 
		:: (n_expired_harvested > LIMIT_EXPIRED) -> has_expired = true;
		:: else                                  -> has_expired = false;
		fi;
		
// check_temperature:
		/*
		 * Get the average temperature between all plants
		 *  use it to check bounds.
		 */
		i = 0;
		do
		:: (i < N_PLANT_BEDS) -> avg_temp = avg_temp + plant_sensors[i].temp; i++;
		:: else -> break;
		od;
		avg_temp = avg_temp / N_PLANT_BEDS;
		if
		:: ((avg_temp > FREEZING_TEMP) && (avg_temp < BURNING_TEMP)) -> temp_in_bounds = true;
		:: else                                                      -> temp_in_bounds = false;;
		fi;

//check_rate_expired:	
		if
		:: (n_expired_harvested == 0)
			-> rate_expired = true;
		:: ((n_expired_harvested != 0) && (((n_mature_harvested+n_expired_harvested) / n_expired_harvested) >= RATE_EXPIRED))
			-> rate_expired = true;
		:: else -> rate_expired = false;
		fi;
		
//check_timed_expired:
		if
		:: (time_step <= TIME_LIMIT) -> timed_expired = has_expired;
		:: else                      -> timed_expired = false;
		fi;

//check_timed_temp:
		if
		:: (time_step <= TIME_LIMIT) -> timed_temp = temp_in_bounds;
		:: else                      -> timed_temp = true;
		fi;
		
//check_timed_rate:
		if
		:: (time_step <= TIME_LIMIT) -> timed_rate = rate_expired;
		:: else                      -> timed_rate = true;
		fi;
	}
	od;
	
}

/**
 * The global clock sends time notifications to every process.
 * If a process has not performed its time-sensitive action yet,
 * the global clock process blocks. 
 */
proctype global_clock()
{
	byte i = 0;
	do
	:: clock[i] ! TIME; 
		if
		:: (i < (N_PROCESSES-1)) -> i++;
		:: else                  -> i = 0; time_step++;
		fi;
	od;
}

/**
 * The global weather influences the temperature of all plants uniformily,
 *  has a longer but random duration during which the rate stays constant.
 */
proctype global_weather(byte my_id)
{
	byte length = 0; // of weather period

	do
	:: atomic {
		clock[my_id] ? _;
		if
		:: length > 0 -> length--;
		:: length == 0 ->
			get_random(length, WEATHER_MIN_LEN, WEATHER_MAX_LEN);
			get_random(weather_temp_rate, WEATHER_MIN_RATE, WEATHER_MAX_RATE);
		fi;
	}
	od;
}

/**
 * Plant beds may contain a plant that grows if the temperature is
 *  in the right range, and report their plant's status as well as
 *  update their state according to the harvesters and seeders.
 */
proctype plant_bed(byte my_id)
{
	byte  growth_rate;
	byte  age = AGE_NO_PLANT;
	short temp = START_TEMP;
	if
	:: (RANDOM_START) -> get_random(age, AGE_NO_PLANT, AGE_MATURE); // random starting age for plant bed
	:: else           -> skip;
	fi;

	do
	:: atomic {
		clock[my_id] ? _;
//update_plant_age:
			/* 
			 * Only grow the plant if it's not expired
			 *  If it's too cold/hot it directly expires
			 */
			if 
			:: ((age < AGE_EXPIRED)
				&& (age != AGE_NO_PLANT))
				-> get_growth_rate(growth_rate, temp);
				    age = age + growth_rate;
					if
					:: (age > AGE_EXPIRED) -> age = AGE_EXPIRED; 
					:: else                -> skip;
					fi;
			:: else -> skip;
			fi;

//update_plant_temperature:
			if
			:: heaters[my_id] -> temp = temp + weather_temp_rate + TEMP_INCREASE;
			:: else           -> temp = temp + weather_temp_rate;
			fi;

//update_plant_sensor:
			plant_sensors[my_id].age = age;
			plant_sensors[my_id].temp = temp;

//receive_action:
			if
			:: plant_action[my_id] ? HARVEST -> 
					assert(age != AGE_NO_PLANT);
					age = AGE_NO_PLANT;
					plant_sensors[my_id].age = age;
			:: plant_action[my_id] ? SEED ->
					assert(age == AGE_NO_PLANT);
					age = AGE_PLANTED;
					plant_sensors[my_id].age = age;
			:: empty(plant_action[my_id]) -> skip;
			fi;
		}
	od;
}

/**
 * The heat manager decides whether each heater should be on or off
 *  by looking at the individual plant's status.
 */
proctype heat_manager(byte my_id)
{
	byte i;
	byte active_heaters = 0;
	short temp;
	do
	:: atomic {
		clock[my_id] ? _;
		i=0;
		do
		:: (i < N_PLANT_BEDS) ->
			temp = plant_sensors[i].temp;
			if
			:: (temp >= (MAX_SAFE_TEMP - HOT_PREEMPTIVE)) ->
					if
					:: (heaters[i]) -> active_heaters--;
					:: else         -> skip;
					fi;
					heaters[i] = false;
			:: (temp <= (MIN_SAFE_TEMP + COLD_PREEMPTIVE)) ->
					if
					:: !(heaters[i]) -> active_heaters++;
					:: else          -> skip;
					fi;
					heaters[i] = true;	
			:: else -> skip;
			fi;
			i++;
		:: else -> break;
		od;
		assert(active_heaters <= N_PLANT_BEDS);
	}
	od;
}


/**
 * Harvester processes harvest plants when they are mature enough.
 */
proctype harvester(byte my_id)
{
	byte i;
	byte j;
	byte my_plants[MY_PLANTS_LEN];
	byte best_plant = 0;
	byte highest_age = 0;

//get_my_plants:
	/*
	 * Every plant has an harvester assigned by index,
	 *  here we save the indexes of the plants assigned to this harvester
	 *  inside the my_plants array.
	 */
	atomic {
		i = 0; j = 0;
		do
		:: (i < N_PLANT_BEDS) -> 
				if
				:: (plant_harvesters[i] == my_id) -> my_plants[j] = i; j++; 
				:: else -> skip;
				fi;
				i++;
		:: else -> break;
		od;
		/*
		 * Empty slots are assigned 255 because the type of indexes is byte
		 *  since we cannot have more than 255 processes and we need
		 *  at least 1 plant and 1 harvester, no plant will have id=255
		 */
		do
		:: (j < MY_PLANTS_LEN) -> my_plants[j] = 255; j++;
		:: else -> break;
		od;
	}

	do
	:: atomic {
		clock[my_id] ? _;
//check_plants:
		/*
		 * The harvesting policy is the highest age heuristic
		 */
		best_plant = 0; i = 0; highest_age = AGE_NO_PLANT;
		do
		:: ((i < MY_PLANTS_LEN) && (my_plants[i] != 255)) -> 
			if
			:: (plant_sensors[my_plants[i]].age > highest_age) -> 
					best_plant = my_plants[i]; highest_age = plant_sensors[my_plants[i]].age;
			:: else -> skip;
			fi;
			i++;
		:: else -> break;
		od;

//harvest_plant:
		if
		:: ((highest_age != AGE_NO_PLANT) && (highest_age > AGE_MATURE)
			&& nfull(plant_action[best_plant])) -> 
				plant_action[best_plant] ! HARVEST;
				if
				:: (plant_sensors[best_plant].age < AGE_EXPIRED) ->
							n_mature_harvested++;
				:: else  -> n_expired_harvested++;
				fi;
		:: (!(highest_age != AGE_NO_PLANT) || !(highest_age > AGE_MATURE)
			|| full(plant_action[best_plant])) -> skip;
		fi;
	}
	od;
}


/**
 * Seeder processes finds empty plant beds and put new seeds in them.
 */
proctype seeder(byte my_id)
{
	byte i;
	byte j;
	byte my_plants[MY_PLANTS_LEN];

//get_my_plants:
	/*
	 * Every plant has a seeder assigned by index,
	 *  analogous to the harvester get_my_plants state
	 */
	atomic {
		i = 0; j = 0;
		do
		:: (i < N_PLANT_BEDS) -> 
				if
				:: (plant_seeders[i] == my_id) -> my_plants[j] = i; j++; 
				:: else -> skip;
				fi;
				i++;
		:: else -> break;
		od;
		do
		:: (j < MY_PLANTS_LEN) -> my_plants[j] = 255; j++;
		:: else                -> break;
		od;
	}

//plant_seeds:
	do
	:: atomic {
		/*
		 * Finds the first plant bed with no plant and just
		 *  plants a seed. Can only plant one seed per time slot.
		 */
		clock[my_id] ? _;
		i = 0;
		do
		:: ((i < MY_PLANTS_LEN) && (my_plants[i] != 255)) -> 
			if
			:: ((plant_sensors[my_plants[i]].age == AGE_NO_PLANT)
				&& nfull(plant_action[my_plants[i]])) -> 
					plant_action[my_plants[i]] ! SEED;
					n_planted++;
					break; // one seed per time slot!
			:: (!(plant_sensors[my_plants[i]].age == AGE_NO_PLANT)
				|| full(plant_action[my_plants[i]])) -> skip;
			fi;
			i++;
		:: else -> break;
		od;
	}
	od;
}


/* INIT */
init {
	byte i = 0;
	byte j = 0;
	byte k = 0; // number of plants assigned to each module
	byte p = 0;

//run_clock:
	run global_clock();

	atomic {
//run_plant_beds:
		do
		:: (i < N_PLANT_BEDS) -> run plant_bed(i); i++;
		:: else -> break;
		od;
		run heat_manager(i); i++;

//assign_plants_to_harvesters:
		// Equally distribute the plants between harvesters
		j = i; p = 0;
		k = N_PLANT_BEDS / N_HARVESTERS;
		do
		:: (j < (N_PROCESSES - N_SEEDERS - 1 - 1)) ->
				k = N_PLANT_BEDS / N_HARVESTERS;
				do
				:: ((k > 0) && (p < N_PLANT_BEDS)) ->
					plant_harvesters[p] = j;
					k--; p++;
				:: else -> break;
				od;
				j++;
		:: else -> break;
		od;
		// assign all remaining plants to the last harvester
		j = (N_PROCESSES - N_SEEDERS - 1 - 1) - 1; // last harvester id
		do
		:: (p < N_PLANT_BEDS) ->
				plant_harvesters[p] = j;
				p++;
		:: else -> break;
		od;

//run_harvesters:
		do
		:: (i < (N_PROCESSES - N_SEEDERS - 1 - 1)) -> run harvester(i); i++;
		:: else -> break;
		od;

//assign_plants_to_seeders:
		// Equally distribute the plants between seeders
		j = i; p = 0;
		k = N_PLANT_BEDS / N_SEEDERS;
		do
		:: (j < (N_PROCESSES - 1 - 1)) ->
				k = N_PLANT_BEDS / N_SEEDERS;
				do
				:: ((k > 0) && (p < N_PLANT_BEDS)) ->
					plant_seeders[p] = j;
					k--; p++;
				:: else -> break;
				od;
				j++;
		:: else -> break;
		od;
		// assign all remaining plants to the last seeder
		j = (N_PROCESSES - 1 - 1) - 1; // last seeder id
		do
		:: (p < N_PLANT_BEDS) ->
				plant_seeders[p] = j;
				p++;
		:: else -> break;
		od;
		
//run_seeders:
		do
		:: (i < (N_PROCESSES - 1 - 1)) -> run seeder(i); i++;
		:: else -> break;
		od;

//run_misc:
		run global_weather(i); i++;
		run monitor(i);
	}
}