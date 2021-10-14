#pragma once
#include <string>

typedef struct PreprocessOutput {
  // number of recursive annotations added
  int numRecursiveFuns;
  // 1 if array types were seen, 0 otherwise
  int usesArrays; // boolean
  // 1 if some other unsupported feature is seen, e.g., varargs, 0 otherwise
  int isUnsupported; // boolean
  // 1 if error occurred while processing the file
  int hasErrorOccurred; // boolean
  // a char buffer to return a string, currently not used for anything
  char* outputBuffer;  
  //...
} PreprocessOutput;