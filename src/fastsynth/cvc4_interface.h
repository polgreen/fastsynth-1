/*
 * cvc4_interface.h
 *
 *  Created on: 9 Dec 2019
 *      Author: elipol
 */

#ifndef SRC_FASTSYNTH_CVC4_INTERFACE_H_
#define SRC_FASTSYNTH_CVC4_INTERFACE_H_

#include "sygus_parser.h"
#include <sstream>

std::string type2sygus(const typet &type);
std::string expr2sygus(const exprt &expr);

class sygus_interfacet
{
public:
    // output sygus file
    void doit(sygus_parsert &sygus_parser);
    std::string declare_vars;
    std::string synth_fun;
    std::string constraints;
    std::string logic;
    void solve();
    std::map<irep_idt, exprt> result;

protected:
    void read_result(std::istream &in);
    void build_query(sygus_parsert &sygus_parser);

    void verify_solution(sygus_parsert &sygus_parser);
};

#endif /* SRC_FASTSYNTH_CVC4_INTERFACE_H_ */
