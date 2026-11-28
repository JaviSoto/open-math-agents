#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using word = long long;

word inverse(word x, word p) {
  word result = 1;
  for (long long r = p-2; r; r /= 2) {
    if (r%2) result = result*x%p;
    x = x*x%p;
  }
  return result;
}

// Independent ordinary row elimination. It uses no recurrence/profile
// identity. Intended only for the small-order audit.
bool nonsingular_by_elimination(int n, word p, const std::vector<int>& support) {
  std::vector<bool> sequence(2*n,false);
  for (const int k : support) if (k<2*n) sequence[k]=true;
  std::vector<std::vector<word>> matrix(n,std::vector<word>(n));
  for (int i=0;i<n;++i)
    for (int j=0;j<n;++j) matrix[i][j]=sequence[i+j];
  for (int col=0;col<n;++col) {
    int pivot=col;
    while (pivot<n && !matrix[pivot][col]) ++pivot;
    if (pivot==n) return false;
    std::swap(matrix[col],matrix[pivot]);
    const word inv=inverse(matrix[col][col],p);
    for (int i=col+1;i<n;++i) if (matrix[i][col]) {
      const word w=(p-matrix[i][col])*inv%p;
      for (int j=col+1;j<n;++j)
        matrix[i][j]=(matrix[i][j]+w*matrix[col][j])%p;
    }
  }
  return true;
}

// For each square Hankel prefix, use the discrepancy algorithm on the
// sequence s[k]=1_{k+2 is a cube}. Its normal indices are precisely the
// lengths n with linear complexity n on the prefix s[0],...,s[2*n-2].
int main(int argc, char **argv) {
  const int max_n = argc>1 ? std::atoi(argv[1]) : 500;
  const word p = argc>2 ? std::atoll(argv[2]) : 1000000007;
  const int exponent = argc>3 ? std::atoi(argv[3]) : 3;
  const bool audit=argc>4 && std::string(argv[4])=="--audit";
  if (max_n<1 || max_n>10000000 || exponent<2 || exponent>3 || p<2 || p>2000000000)
    throw std::invalid_argument("usage: hankel MAX_N PRIME [2|3] [--audit]");
  for (word t=2;t*t<=p;++t)
    if (p%t==0) throw std::invalid_argument("modulus must be prime");
  std::vector<int> support;
  for (word root=2;;++root) {
    word power=1;
    for(int e=0;e<exponent;++e) power *= root;
    if(power>2*max_n) break;
    support.push_back(int(power-2));
  }
  std::vector<word> c{1}, saved{1};
  int length=0, shift=1;
  word inv_previous=1;
  for(int k=0;k<2*max_n-1;++k) {
    word discrepancy=0;
    for(int z:support) {
      if(z>k) break;
      if(k-z<int(c.size())) discrepancy += c[k-z];
    }
    discrepancy %= p;
    if(discrepancy) {
      const bool jump = 2*length<=k;
      std::vector<word> backup;
      if(jump) backup=c;
      const word scale=(p-discrepancy)*inv_previous%p;
      if(c.size()<saved.size()+shift) c.resize(saved.size()+shift,0);
      for (int j=0;j<int(saved.size());++j)
        c[j+shift]=(c[j+shift]+scale*saved[j])%p;
      if(jump) {
        length=k+1-length;
        saved.swap(backup);
        inv_previous=inverse(discrepancy,p);
        shift=0;
      }
    }
    ++shift;
    if(k%2==0) {
      const int n=k/2+1;
      if (audit && (n<=225 || n==350 || n==577)) {
        if (nonsingular_by_elimination(n,p,support)!=(length==n))
          throw std::logic_error("rank disagreement at order "+std::to_string(n));
      }
      if(length!=n) std::cout<<n<<" ";
    }
  }
  std::cout<<"\n";
}
