/* DEFINE  PROPERTIES */
ltl c { <> consensus_reached }
ltl nc { [] !consensus_reached }

/* DEFINE MACROS */
	// hyper-parameters
#define RAND_MIN 0
#define RAND_MAX 100
#define CHANNEL_LEN 5
#define BLOCK_MIN 0
#define BLOCK_MAX 200
#define N_COINS 100


/* DEFINE TYPES */
mtype = { LEADER, VOTE, BLOCK };

/* DEFINE  GLOBAL VARIABLES */
bool consensus_reached = false;
byte random_value = 0;
byte rn;
byte r_count;
byte proof[N_COINS];
byte seed;

/* DEFINE CHANNELS */
//...

/* DEFINE  PROCESSES */
//active proctype
inline randnr(seed, private_key)
{	
	atomic {
		rn = 0;	/* pick random value  */
		//r_count = private_key + seed
		r_count=10;
		do
		:: (r_count>0) && (rn < RAND_MAX) -> rn++; r_count=r_count-1; /* randomly increment */
		//:: (r_count>0) && (rn > RAND_MIN)-> rn--; r_count=r_count-1 /* or decrement */
		:: (r_count>0) -> r_count=r_count-1;
		:: else -> break	/* stop */
		od;
		proof[private_key] = rn;
	}
}


proctype node()
{
	/* allocate variables */
	byte key = 10;

	/* initialize variables */
	// ...

	/* protocol */
	do
	:: atomic {randnr(seed,key); printf("---- THE RANDOM NUMBER IS: %d\n", rn)}
	od;
}

/* INITIALIZE */
init{
	/* allocate */
	byte pid1;

	/* intialize */
	atomic {
		pid1 = run node();
	}
}