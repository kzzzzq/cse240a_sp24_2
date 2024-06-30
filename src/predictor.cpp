//========================================================//
//  predictor.c                                           //
//  Source file for the Branch Predictor                  //
//                                                        //
//  Implement the various branch predictors below as      //
//  described in the README                               //
//========================================================//
#include <stdio.h>
#include <math.h>
#include "predictor.h"
#include <vector>
#include <stdlib.h>
#include <time.h>

//
// TODO:Student Information
//
const char *studentName = "TODO";
const char *studentID = "TODO";
const char *email = "TODO";

//------------------------------------//
//      Predictor Configuration       //
//------------------------------------//

// Handy Global for use in output routines
const char *bpName[4] = {"Static", "Gshare",
                         "Tournament", "Custom"};

// define number of bits required for indexing the BHT here.
int ghistoryBits = 14; // Number of bits used for Global History
int bpType;            // Branch Prediction Type
int verbose;

//------------------------------------//
//      Predictor Data Structures     //
//------------------------------------//

//
// TODO: Add your own Branch Predictor data structures here
//
// gshare
uint8_t *bht_gshare;
uint64_t ghistory;


// TAGE
struct entry {
  int8_t ctr; //3-bit signed saturating counter
  uint8_t tag; //8-bit tag
  uint8_t u; //2-bit useful counter, saturating
};
uint64_t ghistory_sup; //more history bits

entry *T0; //default bimodal predictor
entry *T1;
entry *T2;
entry *T3;
entry *T4;

int bimodal_len = 12;
int tagCom_len = 10; //2^10 entries in each tagged component
int tag_len = 8;
int reset_period = 1 << 18;
int cnt = 0;
bool reset_MSB = true;

uint32_t mask_12 = (1 << 12) - 1; //'hFFF
uint32_t mask_10 = (1 << 10) - 1; //'h3FF
uint32_t mask_8 = (1 << 8) - 1;

int T1_hist_len = 10;
int T2_hist_len = 20;
int T3_hist_len = 40;
int T4_hist_len = 80;

uint16_t CSR[3];//bank2 to bank4, 10 bits
uint8_t CSR1[4];//bank1 to bank4, 8 bits
uint8_t CSR2[4];//7 bits

uint64_t T0_usage = 0; 
uint64_t T1_usage = 0;
uint64_t T2_usage = 0;
uint64_t T3_usage = 0;
uint64_t T4_usage = 0;


//------------------------------------//
//        Predictor Functions         //
//------------------------------------//

/////////////////////////////////// TAGE

void hist_shift(uint64_t* ghistory_ptr, uint64_t* ghistory2_ptr, uint8_t outcome) {
  (*ghistory2_ptr) = (*ghistory2_ptr) << 1;
  uint64_t one = 1;
  uint64_t t = (one << 63);
  uint64_t ghistory_64 = (*ghistory_ptr) / t; //the MSB of ghistory
  (*ghistory2_ptr) = (*ghistory2_ptr) | ghistory_64;
  (*ghistory_ptr) = ((*ghistory_ptr) << 1) | outcome;
}

int get_index(uint32_t pc, int bankNo){
  int pc_9_to_0 = pc & mask_10; //pc[9:0]
  int pc_19_to_10 = (pc >> 10) & mask_10; //pc[19:10]
  if (bankNo == 1){    
    int h_9_to_0 = ghistory & mask_10; //h[9:0]
    return pc_9_to_0 ^ pc_19_to_10 ^ h_9_to_0;
  }
  else { //bank 2 to 4
    int CSR_9_to_0 = CSR[bankNo - 2] & mask_10;
    return CSR_9_to_0 ^ pc_9_to_0 ^ pc_19_to_10;
  }
}

uint8_t get_tag(uint32_t pc, int bankNo){
  uint8_t pc_7_to_0 = pc & mask_8; //pc[7:0]
  return pc_7_to_0 ^ CSR1[bankNo-1] ^ (CSR2[bankNo-1] << 1);
}

void update_CSR_tag(uint8_t* CSR1, uint8_t* CSR2, uint64_t ghistory, uint64_t ghistory_sup){
  uint8_t h_0 = ghistory % 2;

  uint64_t t = 1 << (9 + 1); //the bit evicted
  //uint8_t h_10 = (ghistory & t) / (1 << (9 + 1));
  uint8_t h_10 = (ghistory >> 10) % 2;
  
  t = 1 << (19 + 1); //the bit evicted
  //uint8_t h_20 = (ghistory & t) / (1 << (19 + 1));
  uint8_t h_20 = (ghistory >> 20) % 2;

  t = (uint64_t)1 << (39 + 1); //the bit evicted
  //uint8_t h_40 = (ghistory & t) / ((uint64_t)1 << (39 + 1));
  uint8_t h_40 = (ghistory >> 40) % 2;

  t = 1 << (15 + 1); //the bit evicted
  //uint8_t h_80 = (ghistory_sup & t) / (1 << (15 + 1));
  uint8_t h_80 = (ghistory_sup >> 16) % 2;

  for(int i=0;i<4;i++){
    switch (i)
    {
    case 0 : //bank1
    {
      uint8_t CSR2_3 = (CSR2[0] >> 3) % 2;//CSR2[3] of bank1
      uint8_t CSR2_6 = (CSR2[0] >> 6) % 2;//CSR2[6] of bank1
      uint8_t insert1 = h_0 ^ CSR2_6;
      uint8_t insert2 = h_10 ^ CSR2_3;
      insert2 = insert2 << 4;
      CSR2[0] = (CSR2[0] << 1) | insert1;
      CSR2[0] = (CSR2[0] & (uint8_t)0xEF) | insert2;

      uint8_t CSR1_3 = (CSR1[0] >> 3) % 2;//CSR1[3] of bank1
      uint8_t CSR1_7 = (CSR1[0] >> 7) % 2;//CSR1[7] of bank1
      insert1 = h_0 ^ CSR1_7;
      insert2 = h_10 ^ CSR1_3;
      insert2 = insert2 << 4;
      CSR1[0] = (CSR1[0] << 1) | insert1;
      CSR1[0] = (CSR1[0] & (uint8_t)0xEF) | insert2;
      break;
    }
    case 1 : //bank2
    {
      uint8_t CSR2_3 = (CSR2[1] >> 3) % 2;//CSR2[3] of bank2
      uint8_t CSR2_6 = (CSR2[1] >> 6) % 2;//CSR2[6] of bank2
      uint8_t insert1 = h_0 ^ CSR2_6;
      uint8_t insert2 = h_20 ^ CSR2_3;
      insert2 = insert2 << 4;
      CSR2[1] = (CSR2[1] << 1) | insert1;
      CSR2[1] = (CSR2[1] & (uint8_t)0xEF) | insert2;

      uint8_t CSR1_3 = (CSR1[1] >> 3) % 2;//CSR1[3] of bank2
      uint8_t CSR1_7 = (CSR1[1] >> 7) % 2;//CSR1[7] of bank2
      insert1 = h_0 ^ CSR1_7;
      insert2 = h_20 ^ CSR1_3;
      insert2 = insert2 << 4;
      CSR1[1] = (CSR1[1] << 1) | insert1;
      CSR1[1] = (CSR1[1] & (uint8_t)0xEF) | insert2;
      break;
    }
    case 2 : //bank3
    {
      uint8_t CSR2_3 = (CSR2[2] >> 3) % 2;//CSR2[3] of bank3
      uint8_t CSR2_6 = (CSR2[2] >> 6) % 2;//CSR2[6] of bank3
      uint8_t insert1 = h_0 ^ CSR2_6;
      uint8_t insert2 = h_40 ^ CSR2_3;
      insert2 = insert2 << 4;
      CSR2[2] = (CSR2[2] << 1) | insert1;
      CSR2[2] = (CSR2[2] & (uint8_t)0xEF) | insert2;

      uint8_t CSR1_3 = (CSR1[2] >> 3) % 2;//CSR1[3] of bank3
      uint8_t CSR1_7 = (CSR1[2] >> 7) % 2;//CSR1[7] of bank3
      insert1 = h_0 ^ CSR1_7;
      insert2 = h_40 ^ CSR1_3;
      insert2 = insert2 << 4;
      CSR1[2] = (CSR1[2] << 1) | insert1;
      CSR1[2] = (CSR1[2] & (uint8_t)0xEF) | insert2;
      break;
    }
    case 3 : //bank4
    {
      uint8_t CSR2_3 = (CSR2[3] >> 3) % 2;//CSR2[3] of bank4
      uint8_t CSR2_6 = (CSR2[3] >> 6) % 2;//CSR2[6] of bank4
      uint8_t insert1 = h_0 ^ CSR2_6;
      uint8_t insert2 = h_80 ^ CSR2_3;
      insert2 = insert2 << 4;
      CSR2[3] = (CSR2[3] << 1) | insert1;
      CSR2[3] = (CSR2[3] & (uint8_t)0xEF) | insert2;

      uint8_t CSR1_3 = (CSR1[3] >> 3) % 2;//CSR1[3] of bank4
      uint8_t CSR1_7 = (CSR1[3] >> 7) % 2;//CSR1[7] of bank4
      insert1 = h_0 ^ CSR1_7;
      insert2 = h_40 ^ CSR1_3;
      insert2 = insert2 << 4;
      CSR1[3] = (CSR1[3] << 1) | insert1;
      CSR1[3] = (CSR1[3] & (uint8_t)0xEF) | insert2;
      break;
    }
    default:
      break;
    }
  }
}

void update_CSR_index(uint16_t* CSR, uint64_t ghistory, uint64_t ghistory_sup){
  for(int i=0;i<3;i++){
    switch(i){
      case 0 : //bank2
      {
        uint16_t h_0 = ghistory % 2;
        uint64_t t = 1 << (19 + 1); //the bit evicted
        uint16_t h_20 = (ghistory & t) / (1 << (19 + 1));
        uint16_t CSR_9 = (CSR[0] &  (uint16_t)0x03FF) / (1 << 9);
        CSR[0] = (CSR[0] << 1) | (h_0 ^ h_20 ^ CSR_9);
        break;
      }
      case 1 : //bank3
      {
        uint16_t h_0 = ghistory % 2;
        uint64_t t = (uint64_t)1 << (39 + 1); //the bit evicted
        uint16_t h_40 = (ghistory & t) / ((uint64_t)1 << (39 + 1));
        uint16_t CSR_9 = (CSR[1] &  (uint16_t)0x03FF) / (1 << 9);
        CSR[1] = (CSR[1] << 1) | (h_0 ^ h_40 ^ CSR_9);
        break;
      }
      case 2 : //bank4
      {
        uint16_t h_0 = ghistory % 2;
        uint64_t t = 1 << (15 + 1); //the bit evicted
        uint16_t h_80 = (ghistory_sup & t) / (1 << (15 + 1));
        uint16_t CSR_9 = (CSR[2] &  (uint16_t)0x03FF) / (1 << 9);
        CSR[2] = (CSR[2] << 1) | (h_0 ^ h_80 ^ CSR_9);
        break;
      }
      default:
        break;
      
    }
  }
}

void init_tage() {
  T0 = (entry *)malloc((mask_12 + 1) * sizeof(entry));
  T1 = (entry *)malloc((mask_10 + 1) * sizeof(entry));
  T2 = (entry *)malloc((mask_10 + 1) * sizeof(entry));
  T3 = (entry *)malloc((mask_10 + 1) * sizeof(entry));
  T4 = (entry *)malloc((mask_10 + 1) * sizeof(entry));

  for(int i=0; i<mask_12 + 1; i++){
    T0[i].ctr = 0;
    T0[i].tag = 0;
    T0[i].u = 0;
  }
  for(int i=0; i<(mask_10 + 1); i++){
    T1[i].ctr = 0;
    T1[i].tag = 0;
    T1[i].u = 0;

    T2[i].ctr = 0;
    T2[i].tag = 0;
    T2[i].u = 0;

    T3[i].ctr = 0;
    T3[i].tag = 0;
    T3[i].u = 0;

    T4[i].ctr = 0;
    T4[i].tag = 0;
    T4[i].u = 0;
  }
  for(int i=0; i<3;i++){
    CSR[i] = 0;
  }
  for(int i=0; i<4;i++){
    CSR1[i] = 0;
    CSR2[i] = 0;
  }
  ghistory = 0;
  ghistory_sup = 0;
}

uint8_t tage_predict(uint32_t pc){
  int index[4];
  uint8_t tag[4];
  for(int i=1;i<5;i++){
    index[i-1] = get_index(pc,i); //index to each tagged component
    tag[i-1] = get_tag(pc,i); //tag of each component
  }
  entry indexed_etr[4];
  indexed_etr[0] = T1[index[0]];
  indexed_etr[1] = T2[index[1]];
  indexed_etr[2] = T3[index[2]];  
  indexed_etr[3] = T4[index[3]];

  entry default_etr = T0[(pc & (uint32_t)0x00000FFF)]; //indexed by LS 12 bits of pc
  entry provider = default_etr;
  int provider_num = 0;
  //bool hit = false;
  for(int i=0;i<4;i++){
    if (indexed_etr[i].tag == tag[i]){
      provider = indexed_etr[i];
      provider_num = i + 1;
      //hit = true;
    }
  }
  if (provider_num == 0){
    T0_usage++;
  }
  else if (provider_num == 1){
    T1_usage++;
  }
  else if (provider_num == 2){
    T2_usage++;
  }
  else if (provider_num == 3){
    T3_usage++;
  }
  else{
    T4_usage++;
  }
  

  if (provider.ctr >= 0){
    return TAKEN;
  }
  else {
    return NOTTAKEN;
  }
}

void train_tage(uint32_t pc, uint8_t outcome){
  int index[4];
  uint8_t tag[4];
  for(int i=1;i<5;i++){
    index[i-1] = get_index(pc,i); //index to each tagged component
    tag[i-1] = get_tag(pc,i); //tag of each component
  }
  entry* indexed_etr_ptr[4];
  indexed_etr_ptr[0] = &T1[index[0]];
  indexed_etr_ptr[1] = &T2[index[1]];
  indexed_etr_ptr[2] = &T3[index[2]];  
  indexed_etr_ptr[3] = &T4[index[3]];

  entry* provider = &T0[(pc & (uint32_t)0x00000FFF)];
  entry* altprd = provider;
  int provider_num = 0;

  for(int i=0;i<4;i++){
    if ((*(indexed_etr_ptr[i])).tag == tag[i]){
      altprd = provider;
      provider = indexed_etr_ptr[i];
      provider_num = i + 1; //bankNo of the provider
    }
  }

  uint8_t prd;
  if ((*provider).ctr >= 0){
    prd = TAKEN;
  }
  else {
    prd = NOTTAKEN;
  }

  if (prd == outcome){
    //update provider component's ctr
    if (outcome == TAKEN){
      if ((*provider).ctr < 3){
        (*provider).ctr++;
        if (provider->u == 0){ //update altprd when u counter of the provider is 0
          if (altprd->ctr < 3){
            altprd->ctr++;
          }
        }
      }
    }
    else{
      if ((*provider).ctr > -4){
        (*provider).ctr--;
        if (provider->u == 0){ //update altprd when u counter of the provider is 0
          if (altprd->ctr > -4){
            altprd->ctr--;
          }
        }
      }
    }
  }
  else { //prd is wrong
    //update provider component's ctr
    if (outcome == TAKEN){
      if ((*provider).ctr < 3){
        (*provider).ctr++;
        if (provider->u == 0){ //update altprd when u counter of the provider is 0
          if (altprd->ctr < 3){
            altprd->ctr++;
          }
        }
      }
    }
    else{
      if ((*provider).ctr > -4){
        (*provider).ctr--;
        if (provider->u == 0){ //update altprd when u counter of the provider is 0
          if (altprd->ctr > -4){
            altprd->ctr--;
          }
        }
      }
    }

    std::vector<entry*> allocate_candidate; // {X+1, ..., 4}
    std::vector<entry*> allocate_u_reset; //only 2 useless candidates

    int first_useless_bankNo = 0;
    int second_useless_bankNo = 0;
    int offset = 0;

    if (provider_num < 4){ //provider not using the longest history, allocate a new entry
      for (int i=provider_num + 1; i<4 + 1 ;i++){ //X+1, ..., 4
        allocate_candidate.push_back(indexed_etr_ptr[i - 1]);      
      }
      std::vector<entry*>::iterator itr = allocate_candidate.begin();
      while (itr != allocate_candidate.end()){
        if ((*itr)->u == 0){ //find a useless entry
          allocate_u_reset.push_back(*itr);
          if (allocate_u_reset.size() == 1){
            first_useless_bankNo = provider_num + offset + 1;
          }
          else if (allocate_u_reset.size() == 2){
            second_useless_bankNo = provider_num + offset + 1;
            break;
          }
        }
        offset++;
        itr++;
      }
      if (allocate_u_reset.size() == 0){ //none of the u counters is 0, decrement all u counters and not allocate new entry
        itr = allocate_candidate.begin();
        while (itr != allocate_candidate.end()){
          (*itr)->u = ((*itr)->u - 1) % 4;
          itr++;
        }
      }
      else if (allocate_u_reset.size() == 1){ //the one entry to be stolen
        allocate_u_reset[0]->tag = tag[first_useless_bankNo - 1];
        allocate_u_reset[0]->ctr = (outcome == TAKEN) ? 0 : -1;
        allocate_u_reset[0]->u = 0;
      }
      else {//randomly pick an entry to stole
        //generate a random number between 0 to 2
        srand((unsigned)time(NULL));
        int r = rand() % 3; //0 to 2
        if (r < 2){ //choose the one with shorter history
          allocate_u_reset[0]->tag = tag[first_useless_bankNo - 1];
          allocate_u_reset[0]->ctr = (outcome == TAKEN) ? 0 : -1;
          allocate_u_reset[0]->u = 0;
        }
        else {
          allocate_u_reset[1]->tag = tag[second_useless_bankNo - 1];
          allocate_u_reset[1]->ctr = (outcome == TAKEN) ? 0 : -1;
          allocate_u_reset[1]->u = 0;
        }
      }
    }

    
    
  }
  uint8_t alt = (altprd->ctr >= 0) ? TAKEN : NOTTAKEN; //prediction given by altprd
  if (alt != prd){ //duel
    if (prd == outcome){
      if (provider->u < 3){
        provider->u = (provider->u + 1) % 4;
      }
    }
    else{
      if (provider->u > 0){
        provider->u = (provider->u - 1) % 4;
      }
    }
  }

  //graceful reset
  if (cnt == reset_period -1){
    if (reset_MSB){
      for (int i=0;i<mask_10 + 1;i++){
        T1[i].u = T1[i].u & (uint8_t)0xFD; //reset MSB of u
        T2[i].u = T2[i].u & (uint8_t)0xFD;
        T3[i].u = T3[i].u & (uint8_t)0xFD;
        T4[i].u = T4[i].u & (uint8_t)0xFD;
      }
      reset_MSB = false;
    }
    else{
      for (int i=0;i<mask_10 + 1;i++){
        T1[i].u = T1[i].u & (uint8_t)0xFE; //reset LSB of u
        T2[i].u = T2[i].u & (uint8_t)0xFE;
        T3[i].u = T3[i].u & (uint8_t)0xFE;
        T4[i].u = T4[i].u & (uint8_t)0xFE;
      }
      reset_MSB = true;
    }
  }
  cnt = (cnt + 1) % reset_period;

  //update ghistory, CSR, CSR1 and CSR2
  uint64_t* ghistory_ptr = &ghistory;
  uint64_t* ghistory_sup_ptr = &ghistory_sup;
  hist_shift(ghistory_ptr,ghistory_sup_ptr,outcome);//update ghistory

  update_CSR_index(CSR,ghistory,ghistory_sup); //update CSR for bank2,3,4

  update_CSR_tag(CSR1,CSR2,ghistory,ghistory_sup); //update CSR1 and CSR2 for bank1,2,3,4
  
}
///////////////////////////////////

// Initialize the predictor
//

// gshare functions
void init_gshare()
{
  int bht_entries = 1 << ghistoryBits;
  bht_gshare = (uint8_t *)malloc(bht_entries * sizeof(uint8_t));
  int i = 0;
  for (i = 0; i < bht_entries; i++)
  {
    bht_gshare[i] = WN;
  }
  ghistory = 0;
}

uint8_t gshare_predict(uint32_t pc)
{
  // get lower ghistoryBits of pc
  uint32_t bht_entries = 1 << ghistoryBits;
  uint32_t pc_lower_bits = pc & (bht_entries - 1);
  uint32_t ghistory_lower_bits = ghistory & (bht_entries - 1);
  uint32_t index = pc_lower_bits ^ ghistory_lower_bits;
  switch (bht_gshare[index])
  {
  case WN:
    return NOTTAKEN;
  case SN:
    return NOTTAKEN;
  case WT:
    return TAKEN;
  case ST:
    return TAKEN;
  default:
    printf("Warning: Undefined state of entry in GSHARE BHT!\n");
    return NOTTAKEN;
  }
}

void train_gshare(uint32_t pc, uint8_t outcome)
{
  // get lower ghistoryBits of pc
  uint32_t bht_entries = 1 << ghistoryBits;
  uint32_t pc_lower_bits = pc & (bht_entries - 1);
  uint32_t ghistory_lower_bits = ghistory & (bht_entries - 1);
  uint32_t index = pc_lower_bits ^ ghistory_lower_bits;

  // Update state of entry in bht based on outcome
  switch (bht_gshare[index])
  {
  case WN:
    bht_gshare[index] = (outcome == TAKEN) ? WT : SN;
    break;
  case SN:
    bht_gshare[index] = (outcome == TAKEN) ? WN : SN;
    break;
  case WT:
    bht_gshare[index] = (outcome == TAKEN) ? ST : WN;
    break;
  case ST:
    bht_gshare[index] = (outcome == TAKEN) ? ST : WT;
    break;
  default:
    printf("Warning: Undefined state of entry in GSHARE BHT!\n");
    break;
  }

  // Update history register
  ghistory = ((ghistory << 1) | outcome);
}

void cleanup_gshare()
{
  free(bht_gshare);
}

void init_predictor()
{
  switch (bpType)
  {
  case STATIC:
    break;
  case GSHARE:
    init_gshare();
    break;
  case TOURNAMENT:
    break;
  case CUSTOM:
    init_tage();
    break;
  default:
    break;
  }
}

// Make a prediction for conditional branch instruction at PC 'pc'
// Returning TAKEN indicates a prediction of taken; returning NOTTAKEN
// indicates a prediction of not taken
//
uint32_t make_prediction(uint32_t pc, uint32_t target, uint32_t direct)
{

  // Make a prediction based on the bpType
  switch (bpType)
  {
  case STATIC:
    return TAKEN;
  case GSHARE:
    return gshare_predict(pc);
  case TOURNAMENT:
    return NOTTAKEN;
  case CUSTOM:
    return tage_predict(pc);
  default:
    break;
  }

  // If there is not a compatable bpType then return NOTTAKEN
  return NOTTAKEN;
}

// Train the predictor the last executed branch at PC 'pc' and with
// outcome 'outcome' (true indicates that the branch was taken, false
// indicates that the branch was not taken)
//

void train_predictor(uint32_t pc, uint32_t target, uint32_t outcome, uint32_t condition, uint32_t call, uint32_t ret, uint32_t direct)
{
  if (condition)
  {
    switch (bpType)
    {
    case STATIC:
      return;
    case GSHARE:
      return train_gshare(pc, outcome);
    case TOURNAMENT:
      return;
    case CUSTOM:
      return train_tage(pc, outcome);
    default:
      break;
    }
  }
}
