#include <bits/stdc++.h>
using namespace std;
int main(){
    default_random_engine generator;
    normal_distribution<double> distribution(0.5,0.1);
    for(int i=0; i<=100; i++){
        printf("%f\n", distribution(generator));
    }
    return 0;
}
