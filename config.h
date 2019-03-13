#define NUM_TEST 10

#define NUM_ORG_CLAUSES 218
#define NUM_CLAUSES_PE 1024 m // should < 2^16
#define NUM_VARS 51
#define NUM_PE 64
#define MAX_NUM_LIT 10 //Need to change pos_pid_cls
#define NUM_P 4

#define MAX_DED_LIT 20 //For each BCP, we get at most MAX_DED_LIT literals 

#define BUF_CLS_SIZE 35
#define extra_buf_size 20
#define BUF_DED_SIZE 90
#define BUF_DEC_LVL 100


//#define TF 4
//#define FT 3
#define S 3 //already check the other value
#define U 2
#define F 0
#define T 1

#define NEG 1
#define POS 0


#define SOLVED 0
#define DECISION 1
#define PROP 2
#define DEDUCTION 3
#define ANALYSIS 4
#define FAILED 5
#define EXIT 6
#define BACKTRACK_DEC 7
#define BACKTRACK_DED 8

#define IDLE_32 65535 //0xffff
#define EMPTY 65535
#define IDLE_VAR 255
