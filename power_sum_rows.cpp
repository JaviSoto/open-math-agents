// Evaluate a complete weighted residue block. Share one modular exponentiation
// among all Taylor terms using Horner's rule. See fast_cubic_test.py.
#include <algorithm>
#include <future>
#include <gmpxx.h>
#include <iostream>
#include <stdexcept>
#include <vector>

int main(int argc,char** argv) {
    if (argc<6) throw std::invalid_argument("jobs prime modulus base-exponent coefficients...");
    auto jobs=std::stoul(argv[1]), prime=std::stoul(argv[2]);
    mpz_class modulus(argv[3]), exponent(argv[4]);
    if (!jobs || !prime || modulus<1 || exponent<0) throw std::invalid_argument("invalid block");
    std::vector<mpz_class> coefficients;
    for (int i=5;i<argc;++i) coefficients.push_back(mpz_class(argv[i])%modulus);
    jobs=std::min(jobs,prime);
    std::vector<std::future<mpz_class>> partial;
    for (unsigned long lane=0;lane<jobs;++lane) {
        auto start=prime*lane/jobs, stop=prime*(lane+1)/jobs;
        partial.push_back(std::async(std::launch::async,[&,start,stop] {
            mpz_class acc=0, x, power, value;
            for (unsigned long i=start;i<stop;++i) {
                x=i;
                mpz_powm(power.get_mpz_t(),x.get_mpz_t(),exponent.get_mpz_t(),modulus.get_mpz_t());
                value=coefficients.front();
                for (std::size_t j=1;j<coefficients.size();++j) {
                    value*=i;
                    value+=coefficients[j];
                }
                mpz_addmul(acc.get_mpz_t(),power.get_mpz_t(),value.get_mpz_t());
            }
            mpz_mod(acc.get_mpz_t(),acc.get_mpz_t(),modulus.get_mpz_t());
            return acc;
        }));
    }
    mpz_class answer=0;
    for (auto& task:partial) answer+=task.get();
    std::cout << answer%modulus << '\n';
}
