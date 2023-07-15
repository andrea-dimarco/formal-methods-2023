/* 
 * Automatic Greenhouse
 *  
 * This model consists of a number of plant beds, a heater, harvester bots and seeder bots.
 * There is a global time that forces everything to run in lockstep.
 * Within each plant bed, one plant may be growing if the temperature is within a specific
 * bound. Once the plant is mature, it can be harvested. Otherwise, it will expire due to
 * old age after some more timesteps. The temperature is affected by global weather and
 * a greenhouse heater that is activated when necessary.
 * The harvesters and seeders are each responsible for a fixed set of plant beds and can
 * do one action per timestep.
 */

/** PROPERTIES **/

ltl exp  { [] !(has_expired) } // "the system harvests at most LIMIT_EXPIRED expired plants"
ltl temp { [] temp_in_bounds } // "the average temperature never gets below FREEZING_TEMP or above BURNING_TEMP"
ltl rate { [] rate_expired }   // "the system keeps a rate of 1 (or less) expired plant every RATE_EXPIRED mature plants harvested"

ltl t_exp  { [] !(timed_expired) } // same as 'exp' but only for the first TIME_LIMIT timesteps
ltl t_temp { [] timed_temp }       // same as 'temp' but only for the first TIME_LIMIT timesteps
ltl t_rate { [] timed_rate }       // same as 'rate' but only for the first TIME_LIMIT timesteps

ltl fair_exp { ( ([]<> !(is_harshest_weather)) && ([]<> !(is_longest_weather)) ) -> ([] !(has_expired)) }
ltl fair_temp { ( ([]<> !(is_harshest_weather)) && ([]<> !(is_longest_weather)) ) -> ([] temp_in_bounds)  }
ltl fair_rate { ( ([]<> !(is_harshest_weather)) && ([]<> !(is_longest_weather)) ) -> ([] rate_expired)  }


/** MODEL PARAMETERS **/

/**
 * Number of plant beds, harvesters and seeders. The harvesters and seeders are
 * statically distributed fairly across the plant beds.
 */
#define N_PLANT_BEDS  1
#define N_HARVESTERS  1
#define N_SEEDERS     1

/**
 * Temperature thresholds for plant growth and death.
 * 
 * If the temperature is too low, the plant will freeze (and thus expire).
 * If the temperature is too high, the plant will burn (and thus expire).
 * Above the freezing threshold, the plant makes no growth progress.
 * In the safe interval, it makes normal growth progress.
 * Above the safe temperature range but below burning, the plant grows faster.
 * See the get_growth_rate inline below.
 */
#define FREEZING_TEMP  0
#define MIN_SAFE_TEMP 10
#define MAX_SAFE_TEMP 15
#define BURNING_TEMP  25

/**
 * Starting greenhouse temperature.
 */
#define START_TEMP ((FREEZING_TEMP+BURNING_TEMP)/2)

/**
 * Every timestep, a turned-on heater increases the temperature of all
 * plant beds by this value.
 */
#define HEATING_RATE 4

/**
 * Growth rate of plants depending on the temperature range.
 * See get_growth_rate and the comment on temperatures above.
 */
#define COLD_RATE 0 // (FREEZING_TEMP, MIN_SAFE_TEMP) exclusive
#define SAFE_RATE 1 // [MIN_SAFE_TEMP, MAX_SAFE_TEMP] inclusive
#define HOT_RATE 2  // (MAX_SAFE_TEMP, BURNING_TEMP)  exclusive

/**
 * Plant age thresholds and no-plant marker.
 *
 * Every timestep, the plant age is updated according to the growth rate
 * depending on the temperature. When the plant is mature, it can be harvested,
 * but a while afterwards, it expires. This requires removal by the harvester
 * too, but yields nothing. More broadly, age is used as a sort of plant bed
 * status: there is a marker for when there is no seed planted in the bed,
 * and AGE_EXPIRED also marks plants that froze or overheated.
 */
#define AGE_NO_PLANT 0
#define AGE_PLANTED  1
#define AGE_MATURE   5
#define AGE_EXPIRED 10

/**
 * Weather duration and effect strength.
 *
 * Weather consists of periods of a random length between WEATHER_MIN_LEN
 * and WEATHER_MAX_LEN. Each period has a temperature effect that is
 * added to every plant bed's temperature every timestep. This effect is
 * chosen between WEATHER_MIN_RATE and WEATHER_MAX_RATE and is constant
 * throughout the period.
 *
 * At the moment, we only have cooling weather events, as the plant beds
 * only have heaters and no coolers and we have no way to reasonably
 * react to hot weather.
 */
#define WEATHER_MIN_LEN 1
#define WEATHER_MAX_LEN 3
#define WEATHER_MIN_RATE (-5)
#define WEATHER_MAX_RATE 0

/** CONTROL SYSTEM AND MONITORING PARAMETERS **/

/**
 * Heating system thresholds
 *
 * For the implementation, look at the heat_manager process.
 */
#define COLD_PREEMPTIVE 2 // The heater will be turned ON when temp is this close to safe limits.
#define HOT_PREEMPTIVE  1 // The heater will be turned OFF when the temperature is this close to safe limits.

/**
 * Whether the starting age for the plants is randomized between between
 * [AGE_NO_PLANT, AGE_MATURE]. Otherwise, every plant bed starts empty.
 */
#define RANDOM_START false

/**
 * Knobs for the monitor and properties
 *
 * The monitor process tracks a number of statistics and the properties we can model-check
 * are effectively whether these statistics are within certain bounds.
 */
#define LIMIT_EXPIRED 0 // The number of expired plants the system tolerates before the 'exp' property is violated.
#define RATE_EXPIRED 10 // For the 'rate' property that holds if there is at most one expired plant every 'RATE_EXPIRED' mature harvested plants.
#define TIME_LIMIT   50 // The number of timesteps the system has to satisfy the timed properties (t_*).

/** INTERNAL MACROS **/

#define CHANNEL_LEN 1

/**
 * Upper bound on how many plants can be assigned to a harvester/seeder.
 */
#define HARVESTER_PLANTS_LEN ((N_PLANT_BEDS/N_HARVESTERS)+(N_PLANT_BEDS%N_HARVESTERS))
#define SEEDER_PLANTS_LEN ((N_PLANT_BEDS/N_SEEDERS)+(N_PLANT_BEDS%N_SEEDERS))

/**
 * Time-affected processes.
 *
 * Monitor, heat manager, global weather, plants, harvesters, and seeders.
 */
#define N_PROCESSES (1 + 1 + 1 + N_PLANT_BEDS + N_HARVESTERS + N_SEEDERS)

/** MESSAGE TYPE **/

mtype = { TIME, HARVEST, SEED };

/** GLOBAL VARIABLES **/

/**
 * Temperature and weather are global to all plant beds in the greenhouse,
 * thus best represented as global variables.
 */
short       weather_temp_rate = 0; // See comment about the WEATHER_* parameters.
byte        weather_length = 0;    // length of weather period
bool        heater;                // Is the greenhouse heater turned on?
short       temp = START_TEMP;     // Greenhouse temperature

/**
 * Age readings for each plants. Published every timestep by the plant bed processes.
 * Harvesters and seeders look into this array to find which plants beds to act on.
 */
byte        plant_sensors[N_PLANT_BEDS];

/**
 * Mapping from plant bed to the harvester and seeder that is responsible for it.
 * Statically distributed. The actual value stored is the process number assigned
 * in the INIT section.
 */
byte        plant_harvesters[N_PLANT_BEDS];
byte        plant_seeders[N_PLANT_BEDS];

/**
 * Statistics kept for and by the monitor in order to see which properties are fulfilled.
 */
int         time_step = 0;              // updated by global_clock
byte        n_mature_harvested = 0;     // number of mature plants harvested
byte        n_expired_harvested = 0;    // number of expired plants
bool        has_expired = false;        // for the monitor
bool        temp_in_bounds = true;      // for the monitor
bool        rate_expired = true;        // for the monitor
bool        timed_expired = false;
bool        timed_temp = true;
bool        timed_rate = true;
bool        is_harshest_weather = false;
bool        is_longest_weather = false;

/** CHANNELS **/

/**
 * Array of blocking channels, one for each time-affected process. The global clock
 * sends a TIME message to each process in turn, blocking until it is received,
 * i.e. the process has read the message. Because all processes read the message in
 * an atomic block, this means the process has completely done its action once the
 * global clock is unblocked again.
 *
 * The index of a process is called its ID. Because the IDs of harvesters and seeders
 * are used in other arrays, the order of elements matters and is determined during
 * initialisation (see below).
 */
chan clock[N_PROCESSES] = [0] of { mtype };

/**
 * Every plant bed may receive one HARVEST or SEED action per timestep by its
 * responsible harvester or seeder.
 */
chan plant_action[N_PLANT_BEDS] = [CHANNEL_LEN] of { mtype };

/** INLINES **/

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
inline get_growth_rate(rate)
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


/** PROCESSES **/

/**
 * The monitor is a time-triggered process running at the end of each clock cycle
 * and updates statistics about the system, checking if certain properties are fulfilled.
 * These are exposed above as LTL properties.
 */
proctype monitor(byte my_id)
{
	assert(RATE_EXPIRED > 0);
	assert(TIME_LIMIT > 0);
	assert(LIMIT_EXPIRED >= 0);
	do
	:: atomic { 
		clock[my_id] ? _;
		
// check_expired:
		if 
		:: (n_expired_harvested > LIMIT_EXPIRED) -> has_expired = true;
		:: else                                  -> has_expired = false;
		fi;
		
// check_temperature:		
		if
		:: ((temp > FREEZING_TEMP) && (temp < BURNING_TEMP)) -> temp_in_bounds = true;
		:: else                                              -> temp_in_bounds = false;;
		fi;

//check_rate_expired:	
		if
		:: (n_expired_harvested == 0)
			-> rate_expired = true;
		:: ((n_expired_harvested != 0) && (((n_mature_harvested+n_expired_harvested) / n_expired_harvested) >= RATE_EXPIRED))
			-> rate_expired = true;
			   printf("\n[MONITOR] Expired rate is 1 every (%d) mature\n", ((n_mature_harvested+n_expired_harvested) / n_expired_harvested));
		:: else -> rate_expired = false;
			   printf("\n[MONITOR] Expired rate is 1 every (%d) mature\n", ((n_mature_harvested+n_expired_harvested) / n_expired_harvested));
		fi;
		
//check_timed_expired:
		if
		:: (time_step <= TIME_LIMIT) -> timed_expired = has_expired;
		:: else                      -> timed_expired = false;
		fi;
		/*
		if
		:: (timed_expired) -> assert(false);
		:: else -> skip;
		fi;
		*/

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

//check_fairness:
		if
		:: (weather_temp_rate == WEATHER_MIN_RATE) -> is_harshest_weather = true;
		:: else                                    -> is_harshest_weather = false;
		fi;
		if
		:: (weather_length == WEATHER_MAX_LEN) -> is_longest_weather = true;
		:: else                                -> is_longest_weather = false;
		fi;
	}
	od;
	
}

/**
 * The global clock cyclically sends time notifications to every process.
 * As long as a process has not completed its time-triggered action yet,
 * the global clock process blocks.
 */
proctype global_clock()
{
	byte p = 0;
	do
	:: clock[p] ! TIME; 
		if
		:: (p < (N_PROCESSES-1)) -> p++;
		:: else                  -> p = 0; time_step++;
		fi;
	od;
}

/**
 * The global weather influences the temperature of all plants uniformily,
 * and has a random duration during which this weather effect stays constant.
 * See the comment on the WEATHER_* parameters.
 */
proctype global_weather(byte my_id)
{
	do
	:: atomic {
		clock[my_id] ? _;
		if
		:: weather_length > 0  -> weather_length--;
		:: weather_length == 0 ->
			get_random(weather_length, WEATHER_MIN_LEN, WEATHER_MAX_LEN);
			get_random(weather_temp_rate, WEATHER_MIN_RATE, WEATHER_MAX_RATE);
		:: else -> assert(false);
		fi;
	}
	od;
}

/**
 * Plant beds are either empty or contain a plant that grows if the 
 * temperature is in the right range. They report the plant status
 * and update their state in response to plant_action messages by
 * harvesters and seeders.
 */
proctype plant_bed(byte my_id)
{
	byte  growth_rate;
	byte  age = AGE_NO_PLANT;
	if
	:: (RANDOM_START) -> get_random(age, AGE_NO_PLANT, AGE_MATURE); // random starting age for plant bed
	:: else           -> skip;
	fi;

	do
	:: atomic {
		clock[my_id] ? _;
//update_plant_age:
			/* 
			 * Only grow the plant if it's not expired.
			 * If it's too cold/hot it directly expires.
			 */
			if 
			:: ((age < AGE_EXPIRED)
				&& (age != AGE_NO_PLANT))
				-> get_growth_rate(growth_rate);
				    age = age + growth_rate;
					if
					:: (age > AGE_EXPIRED) -> age = AGE_EXPIRED; 
					:: else                -> skip;
					fi;
			:: else -> skip;
			fi;

//update_plant_sensor:
			plant_sensors[my_id] = age;

//receive_action:
			if
			:: plant_action[my_id] ? HARVEST -> 
					assert(age != AGE_NO_PLANT);
					age = AGE_NO_PLANT;
					plant_sensors[my_id] = age;
			:: plant_action[my_id] ? SEED ->
					assert(age == AGE_NO_PLANT);
					age = AGE_PLANTED;
					plant_sensors[my_id] = age;
			:: empty(plant_action[my_id]) -> skip;
			fi;
		}
	od;
}

/**
 * The heat manager decides whether the heater should be on or off.
 */
proctype heat_manager(byte my_id)
{
	assert((MAX_SAFE_TEMP - HOT_PREEMPTIVE) > (MIN_SAFE_TEMP + COLD_PREEMPTIVE));
	do
	:: atomic {
		clock[my_id] ? _;
//update_plant_temperature:
		if
		:: heater -> temp = temp + weather_temp_rate + HEATING_RATE;
		:: else   -> temp = temp + weather_temp_rate;
		fi;
//manage_heater:
		if
		:: (temp >= (MAX_SAFE_TEMP - HOT_PREEMPTIVE)) ->
				heater = false;
		:: (temp <= (MIN_SAFE_TEMP + COLD_PREEMPTIVE)) ->
				heater = true;	
		:: else ->
				skip;
		fi;
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
	byte my_plants[HARVESTER_PLANTS_LEN];
	byte best_plant = 0;
	byte highest_age = 0;

//get_my_plants:
	/*
	 * Every plant bed has an harvester assigned based on its index.
	 * Save the indices of the plants beds assigned to this
	 * harvester inside the my_plants array.
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
		 * Empty slots are assigned 255 because the type of indices is byte.
		 * Since we cannot have more than 255 processes and we need
		 * at least one plant bed and one harvester, no plant will have ID 255.
		 */
		do
		:: (j < HARVESTER_PLANTS_LEN) -> my_plants[j] = 255; j++;
		:: else -> break;
		od;
	}

	do
	:: atomic {
		clock[my_id] ? _;
//check_plants:
		/*
		 * Harvesting policy: choose oldest mature plant.
		 */
		best_plant = 0; i = 0; highest_age = AGE_NO_PLANT;
		do
		:: ((i < HARVESTER_PLANTS_LEN) && (my_plants[i] != 255)) -> 
			if
			:: (plant_sensors[my_plants[i]] > highest_age) -> 
					best_plant = my_plants[i]; highest_age = plant_sensors[my_plants[i]];
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
				:: (plant_sensors[best_plant] < AGE_EXPIRED) ->
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
 * Seeder processes find empty plant beds and put new seeds in them.
 * They are dual to harvesters and as such are mostly a copy, implementation-wise.
 */
proctype seeder(byte my_id)
{
	byte i;
	byte j;
	byte my_plants[SEEDER_PLANTS_LEN];

//get_my_plants:
	/*
	 * Every plant has a seeder assigned by index, analogously to the harvester.
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
		:: (j < SEEDER_PLANTS_LEN) -> my_plants[j] = 255; j++;
		:: else                -> break;
		od;
	}

//plant_seeds:
	do
	:: atomic {
		/*
		 * Seeding policy: Find the first plant bed with no plant an
		 * plant a seed. Can only plant one seed per time slot.
		 */
		clock[my_id] ? _;
		i = 0;
		do
		:: ((i < SEEDER_PLANTS_LEN) && (my_plants[i] != 255)) -> 
			if
			:: ((plant_sensors[my_plants[i]] == AGE_NO_PLANT)
				&& nfull(plant_action[my_plants[i]])) -> 
					plant_action[my_plants[i]] ! SEED;
					break; // one seed per time slot!
			:: (!(plant_sensors[my_plants[i]] == AGE_NO_PLANT)
				|| full(plant_action[my_plants[i]])) -> skip;
			fi;
			i++;
		:: else -> break;
		od;
	}
	od;
}

/** INIT **/

init {
	byte i = 0; // process ID used in clock[] array
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
		/*
		 * Equally distribute the plants between harvesters.
		 */
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
		/*
		 * Assign all remaining plants to the last harvester.
		 */
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
		/*
		 * Equally distribute the plants between seeders.
		 */
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
		/*
		 * Assign all remaining plants to the last seeder.
		 */
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
