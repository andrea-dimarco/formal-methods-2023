/* DEFINE  PROPERTIES */
ltl c { <> consensus_reached } /* in the future consensus will be reached */

/* DEFINE MACROS */
	// hyper-parameters
#define N_COINS 20       // amount of coins in the network
#define N_NODES 10       // total amount of nodes
#define N_BYZANTINE 2    // byzantine nodes
#define COMMITTEE_SIZE 5 // minimun amount of nodes in the committee

	// wealth distribution parameters
#define EQUAL_DISTRIBUTION true // if the coins are to be distributed equally or randomly
#define MIN_COINS 1             // MIN and MAX amount of coins that one node can have 
#define MAX_COINS 2             //   if the wealth is NOT equally distributed

	// danger zone: do not change these
#define RAND_MIN 0     // lower bound for the random number generator
#define RAND_MAX 10    // upper bound for the random number generator
#define CHANNEL_LEN 5  // Max messages in the FIFO
#define SEED 0         // public seed (aka the last block we achieved consensus on)


/* DEFINE TYPES */
mtype = { COMMITTEE, VOTE, BLOCK, RECOVERY, ACK };

/* DEFINE  GLOBAL VARIABLES */
bool consensus_reached = false;
byte random_value = 0;
byte r_count;
byte proof[N_COINS];
byte coins[N_NODES];

chan node_2_relay[N_NODES];
chan relay_2_nodes[N_NODES];

/* DEFINE CHANNELS */
//...

/* DEFINE  PROCESSES */
/**
 * Saves a random number in [min, max]
 * inside the variable rn
 */
inline rand_bounded(rn, min, max)
{	
	d_step {
		rn = min;
		r_count = max - min;
		do
		:: (r_count>0) && (rn < max) -> rn++; r_count=r_count-1; /* randomly increment */
		:: (r_count>0) -> r_count=r_count-1;                     /* randomly do nothing */
		:: else -> break	                                     /* stop */
		od;
	}
}


inline lottery(seed, private_key, ticket, dumb_byzantine)
{	
	d_step {
		if
		:: dumb_byzantine ->
				ticket = true;
				proof[private_key] = false; // cryptography will unmask the byzantine proofs
		:: else ->
				if
				:: true -> ticket = true;
				:: true -> ticket = false;
				fi;
				proof[private_key] = ticket;
		fi;
	}
}


proctype node(byte id, byzantine)
{
	/* allocate variables */
	byte key = 10;
	bool ticket = false;
	bool dumb_byzantine = false;
	bool smart_byzantine = false;

	/* initialize variables */
	initialize_node:
		atomic {
			if /* different types of byzantine attack */
			:: byzantine -> dumb_byzantine=true; smart_byzantine=true;
			:: byzantine -> dumb_byzantine=false;smart_byzantine=true;
			:: else -> dumb_byzantine=false;smart_byzantine=false;
			fi;
			// ...
		}

	/* protocol */
	// ...
	
}

/* All messages are sent to relay nodes which will propagate them through the net */
/*  without loss of generality we can have just one relay node */
proctype relay_node(chan in, out)
{
	skip;
}


/* INITIALIZE */
init{
	/* allocate */
	byte pid1;
	byte pid_relay;
	short i = 0;
	short j = 0;
	short k = 0;

	/* distribute wealth */
	atomic {
		assert(N_COINS >= N_NODES);
		if
		:: EQUAL_DISTRIBUTION ->
			equal_wealth:
				i = 0; // node id
				j = 0; // coin id
				k = N_COINS/N_NODES; // floor integer value, exess coins are lost
				do
				:: (i < N_NODES) -> 
							k = N_COINS/N_NODES;
							do
							:: ((k > 0) && (j < N_COINS)) ->
										coins[j] = i;
										j++;
										k--;
							:: else -> break;
							od;
							i++;
				:: else -> break;
				od;
		:: else ->
			unequal_wealth:
				assert(N_COINS >= (MIN_COINS*N_NODES));
				i = 0; // node id
				j = 0; // coin id
				k = MIN_COINS; // coin count
				do /* assign minimum coins to everyone */
				:: (i < N_NODES) -> 
							k = MIN_COINS;
							do
							:: ((k > 0) && (j < N_COINS)) ->
										coins[j] = i;
										j++;
										k--;
							:: else -> break;
							od;
							i++;
				:: else -> break;
				od;
				i = 0;
				do
				:: (i < N_NODES) -> 
								// write in k a random number
								// between 
									// 0 := no coins
									// max-min := all remaining coins allowed
							rand_bounded(k, 0,  MAX_COINS-MIN_COINS)
							do
							:: ((k > 0) && (j < N_COINS)) ->
										coins[j] = i;
										j++;
										k--;
							:: else -> break;
							od;
							i++;
				:: else -> break;
				od;
		fi;
	}

	/* intialize nodes */
	atomic {
		// relay node
		i = 0;
		do
		:: (i < N_NODES) -> 
				node_2_relay[i] = [CHANNEL_LEN] of { mtype, byte, byte };
				relay_2_nodes[i] = [CHANNEL_LEN] of { mtype, byte, byte };
				i++;
		:: else -> break;
		od;
		pid_relay = run relay_node(node_2_relay, relay_2_nodes);

		// normal nodes
		pid1 = run node(0, 0);
	}


}