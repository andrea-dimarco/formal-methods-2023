/* PROPERTIES */
ltl c { <> consensus_reached } /* in the future consensus will be reached */

/* MACROS */
	// hyper-parameters
#define N_COINS 10       // amount of coins in the network (must be < END_COMM)
#define N_NODES 2       // total amount of nodes
#define N_BYZANTINE 1    // byzantine nodes
#define COMMITTEE_SIZE 5 // minimun amount of winning tickets in the committee
#define BYZANTINE_COINS_PERCHENTAGE 25 // perchentage of coins that can be own byzantine nodes

	// wealth distribution parameters
#define EQUAL_DISTRIBUTION true // if the coins are to be distributed equally or randomly
#define MIN_COINS 1             // MIN and MAX amount of coins that one node can have 
#define MAX_COINS 2             //   if the wealth is NOT equally distributed

	// danger zone: do not change these
#define CHANNEL_LEN 10  // Max messages in the FIFO
#define SEED 0         // public seed (aka the last block we achieved consensus on)
#define MIN_RAND 1
#define MAX_RAND 3
#define END_COMM 255


/* DEFINE TYPES */
mtype = { COMMITTEE, VOTE, ACK, LOTTERY, BLOCK };

/* DEFINE  GLOBAL VARIABLES */
bool consensus_reached = false; // if the protocol reached consensus
byte r_count; // need this for the random number macro
byte proof[N_COINS]; // this stores the proof for the VRF (aka lottery) of every coin
byte coins[N_COINS]; // every coin has a node assigned to it

/* DEFINE CHANNELS */
chan node_2_relay[N_NODES] = [CHANNEL_LEN] of { mtype, byte, byte };; // messages from nodes to the relay
chan relay_2_nodes[N_NODES] = [CHANNEL_LEN] of { mtype, byte, byte };; // messages from the relay to the nodes

/* UTILITIES */
/**
 * Saves a random number in [min, max] inside the variable rn
 */
inline rand_bounded(rn, min, max)
{	
	atomic {
		assert(min <= max);
		rn = min;
		r_count = max - min;
		do
		:: (r_count>0) && (rn < max) -> rn++; r_count=r_count-1; /* randomly increment */
		:: (r_count>0) -> r_count=r_count-1;                     /* randomly do nothing */
		:: else -> break	                                     /* stop */
		od;
	}
}


/**
 * Saves the result of the thresholded VRF in the ticket variable and the proof in the global array proofs.
 *  This is a nondeterministic choice.
 *  If the node is byzantine then the ticket will be true but the proof will be false.
 */
inline lottery(seed, private_key, ticket, byzantine_dumb)
{	
	atomic {
		if
		:: ticket = 1; proof[private_key] = true;
		:: ticket = 0; proof[private_key] = false;
				if
				:: byzantine_dumb ->
						ticket = 1;
						proof[private_key] = false; // cryptography will unmask the byzantine proofs
				:: else -> skip;
				fi;
		fi;
	}
}


/* PROCESSES */
/**
 * Normal node of the systems.
 *  Owns an amount of coins and follows the Algorand protocol phases.
 */
proctype node(byte my_id, byzantine)
{
	/* allocate variables */
	bool byzantine_dumb = false;
	bool byzantine_smart = false;

	byte ticket = 0;
	byte my_coins[N_COINS]; // indexes of the coins this node owns
	byte n_my_coins; // number of coins the node owns
	byte winning_coins[N_COINS]
	byte n_winning_coins;
	byte signature;
	byte foo;
	byte block; // the block this node wll propose if it manages to win the lottery
	byte i;
	byte j;

	/* initialize variables */
initialize_node:
	atomic {
		// byzantine node
		if /* different types of byzantine attack */
		:: (byzantine) -> byzantine_dumb=true;
		:: (byzantine) -> byzantine_dumb=false;
		:: else -> skip;
		fi;
		byzantine_smart = byzantine; 

		// retrieve coins
		i = 0; j = 0; n_my_coins = 0;
		do
		:: ((i<N_COINS) && (j<N_COINS) && (coins[j] == my_id)) ->	n_my_coins++; my_coins[i] = j; i++; j++;
		:: ((i<N_COINS) && (j<N_COINS) && (coins[j] != my_id)) -> j++;
		:: ((i<N_COINS) && (j>=N_COINS)) -> my_coins[i] = END_COMM; i++;
		:: else -> break;
		od;
		i = 0; j = 0;

		// initialize all variables
		i = 0;
		do
		:: (i<N_COINS) -> winning_coins[i] = END_COMM; i++;
		:: else -> break;
		od;
		i = 0; j = 0; signature = 0; block = 0; n_winning_coins = 0; foo = 0;
	}
	printf("\n\n[NODE_0%d] I'm node [%d] and I have (%d) coins.\n\n", _pid, my_id, n_my_coins);

	/* protocol finally begins */
coin_lottery_1:
	/* call in the lottery and see if the coins won */ 
	atomic {
		i = 0; j = 0;
		do
		:: (i < n_my_coins) -> 
				/* call lottery */
				lottery(SEED, my_coins[i], ticket, byzantine_dumb)
				/* send result to relay */
				node_2_relay[my_id] ! LOTTERY(my_coins[i], ticket);
				if
				:: (ticket == 1) -> n_winning_coins++; winning_coins[j] = my_coins[i]; j++;
				:: else -> skip;
				fi;
				i++;
		:: else -> break;
		od;
		// tell the relay we are done
		node_2_relay[my_id] ! LOTTERY(END_COMM, END_COMM);
		printf("\n\n[NODE_0%d] I'm node [%d] and I have (%d) winning coins.\n\n", _pid, my_id, n_winning_coins);
	}
lottery_ack_1:
	/* receive ack from the relay */
	atomic {
		i = 0; n_winning_coins = 0;
		do
		:: (i < (n_my_coins+1)) -> 
				relay_2_nodes[my_id] ? ACK, signature, foo;
				printf("\n\n[NODE_0%d] I'm [%d] and received <%d,%d>\n\n", _pid, my_id, signature, foo);
				if
				:: ((signature == END_COMM) && (foo == END_COMM)) -> break; // end comm
				:: ((foo) && (signature != END_COMM)) -> winning_coins[i]=signature; n_winning_coins++; i++;
				:: else -> skip;
				fi;
		:: else -> break;
		od; 
		printf("\n\n[NODE_0%d] I'm node [%d] and I have (%d) winning coins.\n\n", _pid, my_id, n_winning_coins);
	}

generate_block:
	atomic {
		if
		:: (n_winning_coins == 0) -> goto committee_lottery; // Might still be part of the committee
		:: else -> skip;
		fi;
			// the block is a random number
		rand_bounded(block, SEED+1, MAX_RAND); // stores a random value in block
		printf("\n\n[NODE_0%d] I'm node [%d] and proposing the block (%d).\n\n", _pid, my_id, block);
	}

propose_block:
	atomic {
		/* 
		 * Propose block
		 *  Send the block to the relay node once.
		 *   regardless of how many winning tickets the node has.
		 */
		node_2_relay[my_id] ! BLOCK(my_id, block);
	}

receive_blocks:
	/*
	 * Receive all the blocks that have been generated.
	 *  keep the one with the smallest value,
	 *  if byzantine, keep a random block.
	 */
	atomic {
		do
		:: relay_2_nodes[my_id] ? BLOCK, _, foo; ->
				if
				:: (foo == END_COMM) -> break;
				:: else -> 
						if
						:: (byzantine_smart) -> block = foo;   // keep the block
						:: (byzantine_smart) -> skip;          // loose the block
						:: (foo < block) -> block = foo; // normal beheavior
						:: else -> skip;
						fi;
				fi;
		od;
	}

committee_lottery:
	atomic {
		skip;
	}

end_protocol:
	skip;
}

/* All messages are sent to relay nodes which will propagate them through the net */
/*  without loss of generality we can have just one relay node */
proctype relay_node()
{
	/* Allocate vaiables */
	byte ticket;
	byte coin_lottery[N_COINS];
	byte signature;
	byte lottery_winners;
	byte i;
	byte j;
	byte k;

	/* nodes call the lottery to choose a value */
	// we must check that enough nodes won the lottery
	// otherwise we have to activate the recovery mode
lottery_winners_check_1:
	atomic {
			// count winners
		i = 0; lottery_winners = 0;
		do
		:: (i < N_NODES) -> 
				// a single node might have multiple coins
				// get the lottery result
				// no proof check
				node_2_relay[i] ? LOTTERY, signature, ticket;
				if
				:: (ticket == END_COMM) -> i++; // end comm, go to next node
				:: (ticket == 1) -> coin_lottery[signature] = 1; lottery_winners++;
				:: (ticket == 0) -> coin_lottery[signature] = 0;
				:: else -> assert(false);
				fi;
				printf("\n\n[RELAY] Received(%d) with sign [%d] from node [%d].\n\n", ticket, signature,i);
		:: else -> break;
		od;
		if // choose what to do
		:: (lottery_winners < COMMITTEE_SIZE) -> goto recovery_mode_1;
		:: else -> goto send_acks_1;
		fi;
	}
	printf("\n\n[RELAY] There are (%d) winning tokens.\n\n", lottery_winners);
	/* RECOVERY MODE
	 *  Force nodes to generate a block
	 *   until we have enough blocks for
	 *   the problem to be interesting to analyze
	 */
recovery_mode_1:
	atomic {
		i = 0; j = COMMITTEE_SIZE-lottery_winners;
		assert(j>=0);
		do
		:: ((j < N_COINS) && (k > 0)) ->
				if
				:: !(coin_lottery[j]) -> coin_lottery[j] = true; proof[j] = true; k--; 
				:: else -> skip;
				fi;
				j++; 
		:: else -> break;
		od;
	}

send_acks_1:
	atomic {
		i = 0; j = 0;
		do
		:: (i < N_NODES) -> 
				j = 0;
				do
				:: (j < N_COINS) ->
						if
						:: ((coins[j] == i)) -> relay_2_nodes[i] ! ACK(j, coin_lottery[j]);
												printf("\n\n[RELAY] Sending <%d,%d> to [%d]\n\n",j,coin_lottery[j],i);
						:: else -> skip;
						fi;
						j++;
				:: else -> break;
				od;
				relay_2_nodes[i] ! ACK(END_COMM, END_COMM); // end comm
				i++;
		:: else -> break;
		od;
		goto relay_blocks;
	}

	/* start propagating generated blocks */
relay_blocks:
		/* receive blocks */
	atomic {
		// nodes send only one block
		// only nodes that won at least one ticket will send a block
		skip;
	}
}


/* INITIALIZE */
init{
	/* allocate */
	byte pid1;
	byte pid_relay;
	short i;
	short j;
	short k;
	bool is_byzantine;
	chan tmp_chan;

	assert(SEED < MAX_RAND);
	/* distribute wealth */
	assert(N_COINS < END_COMM);
	atomic {
		assert(N_COINS >= N_NODES);
		if
		:: EQUAL_DISTRIBUTION ->
			equal_wealth:
				i = 0; // node id
				j = 0; // coin id
				k = N_COINS/N_NODES; // floor integer value, exess coins are lost
				do
				:: (i < N_NODES)-> 
							k = N_COINS/N_NODES;
							printf("\nNode [%d] has (%d) coins.\n\n", i, k);
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
		pid_relay = run relay_node();

		// normal nodes
		pid1 = run node(0, true);
		pid1 = run node(1, false);
		skip;
	}
	


}