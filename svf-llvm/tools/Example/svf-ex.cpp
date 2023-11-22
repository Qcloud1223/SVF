//===- svf-ex.cpp -- A driver example of SVF-------------------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===-----------------------------------------------------------------------===//

/*
 // A driver program of SVF including usages of SVF APIs
 //
 // Author: Yulei Sui,
 */

#include "SVF-LLVM/LLVMUtil.h"
#include "AbstractExecution/SVFIR2ItvExeState.h"
#include "Graphs/SVFG.h"
#include "WPA/Andersen.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "Util/CommandLine.h"
#include "Util/Options.h"
#include "SVF-LLVM/LLVMModule.h"

/* DDA related */
#include "DDA/DDAPass.h"
#include "DDA/FlowDDA.h"
#include "DDA/DDAClient.h"

using namespace std;
using namespace SVF;

/*!
 * An example to query alias results of two LLVM values
 */
SVF::AliasResult aliasQuery(PointerAnalysis* pta, SVFValue* v1, SVFValue* v2)
{
    return pta->alias(v1,v2);
}

/*!
 * An example to print points-to set of an LLVM value
 */
std::string printPts(PointerAnalysis* pta, const SVFValue* val)
{

    std::string str;
    std::stringstream rawstr(str);

    NodeID pNodeId = pta->getPAG()->getValueNode(val);
    const PointsTo& pts = pta->getPts(pNodeId);
    for (PointsTo::iterator ii = pts.begin(), ie = pts.end();
            ii != ie; ii++)
    {
        rawstr << " " << *ii << " ";
        PAGNode* targetObj = pta->getPAG()->getGNode(*ii);
        if(targetObj->hasValue())
        {
            rawstr << "(" << targetObj->getValue()->toString() << ")\t ";
        }
    }

    return rawstr.str();

}

/*!
 * An example to query/collect all SVFStmt from a ICFGNode (iNode)
 */
void traverseOnSVFStmt(const ICFGNode* node)
{
    SVFIR2ItvExeState* svfir2ExeState = new SVFIR2ItvExeState(SVFIR::getPAG());
    for (const SVFStmt* stmt: node->getSVFStmts())
    {
        if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            svfir2ExeState->translateAddr(addr);
        }
        else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
        {
            svfir2ExeState->translateBinary(binary);
        }
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            svfir2ExeState->translateCmp(cmp);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            svfir2ExeState->translateLoad(load);
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            svfir2ExeState->translateStore(store);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            svfir2ExeState->translateCopy(copy);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            if (gep->isConstantOffset())
            {
                gep->accumulateConstantByteOffset();
                gep->accumulateConstantOffset();
            }
            svfir2ExeState->translateGep(gep);
        }
        else if (const SelectStmt *select = SVFUtil::dyn_cast<SelectStmt>(stmt))
        {
            svfir2ExeState->translateSelect(select);
        }
        else if (const PhiStmt *phi = SVFUtil::dyn_cast<PhiStmt>(stmt))
        {
            svfir2ExeState->translatePhi(phi);
        }
        else if (const CallPE *callPE = SVFUtil::dyn_cast<CallPE>(stmt))
        {
            // To handle Call Edge
            svfir2ExeState->translateCall(callPE);
        }
        else if (const RetPE *retPE = SVFUtil::dyn_cast<RetPE>(stmt))
        {
            svfir2ExeState->translateRet(retPE);
        }
        else
            assert(false && "implement this part");
    }
}


/*!
 * An example to query/collect all successor nodes from a ICFGNode (iNode) along control-flow graph (ICFG)
 */
void traverseOnICFG(ICFG* icfg, const ICFGNode* iNode)
{
    FIFOWorkList<const ICFGNode*> worklist;
    Set<const ICFGNode*> visited;
    worklist.push(iNode);

    /// Traverse along VFG
    while (!worklist.empty())
    {
        const ICFGNode* vNode = worklist.pop();
        for (ICFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                    vNode->OutEdgeEnd(); it != eit; ++it)
        {
            ICFGEdge* edge = *it;
            ICFGNode* succNode = edge->getDstNode();
            if (visited.find(succNode) == visited.end())
            {
                visited.insert(succNode);
                worklist.push(succNode);
            }
        }
    }
}

/* traverse VFG and find definition for only 1 layer */
void singleLayerVFGCallback(const SVFG *vfg, Set<const VFGNode *> &visited)
{
    for(Set<const VFGNode*>::const_iterator it = visited.begin(), eit = visited.end(); it!=eit; ++it)
    {
        /* Generic VFG and node usages:
         * vfg->getLHSTopLevPtr(node): get a node's LHS top level pointer. Not sure what it used for
         * vfg->getRHSVar/getLHSVar(): get a node's LHS/RHS variable. Not sure why the above iface is a separate one
         */
        const VFGNode* node = *it;
        if (const LoadVFGNode *ln = SVFUtil::dyn_cast<LoadVFGNode>(node)) {
            SVFUtil::outs() << "Loading object at " << ln->getValue()->getSourceLoc();
            /* LoadVFGNode usages:
             * ln->toString(): get raw LLVM instructions
             * ln->getValue(): get SVF value of node. Quite similar with LLVM Value
             * ln->getDefSVFGNode(): get definition of current node. Hopefully it's the top-level one
             * ln->getDefSVFVars(): Return a BV containing definition variables (ID correspond to ConsG)
             *      Not sure what this iface is used for
             */
            const SVFGNode *def = vfg->getDefSVFGNode(ln->getPAGSrcNode());
            /* Loading from a struct/array, and thus GEP */
            if (const GepVFGNode *gep_def = SVFUtil::dyn_cast<GepVFGNode>(def)) {
                const GepStmt *gs = SVFUtil::dyn_cast<GepStmt>(gep_def->getPAGEdge());
                SVFUtil::outs() << ", Index: " << gs->getConstantFieldIdx() << "\n";
            } 
            /* Loading directly from a global variable, easy */
            else if (const AddrVFGNode *addr_def = SVFUtil::dyn_cast<AddrVFGNode>(def)) {
                const AddrStmt *ads = SVFUtil::dyn_cast<AddrStmt>(addr_def->getPAGEdge());
                assert(ads);
                SVFUtil::outs() << "\n";
            }
            /* Important: fail-safe way of handling source nodes */
            else {
                assert(false && "Load is not from a GEP or ADDR! Debug for more info!\n");
            }
        }
        // else if (const GepVFGNode *gn = SVFUtil::dyn_cast<GepVFGNode>(node)) {
        //     /* GepVFGNode usages:
        //      * gn->toString(): get raw LLVM instructions
        //      * gn->getPAGEdge(): get PAG edge, which is a statement
        //      * gn->getPAGEdge()->getSrcID()/getDstID(): get src/dst operand for this edge
        //      * gs->getConstantFieldIdx(): get constant field offset of a Gep statement
        //      */
        //     const GepStmt *gs = SVFUtil::dyn_cast<GepStmt>(gn->getPAGEdge());
        //     SVFUtil::outs() << "GEP at Src: " << gn->getPAGEdge()->getSrcID() << ", index: " << gs->getConstantFieldIdx() << "\n";
        // }
        else if (const StoreVFGNode *svn = SVFUtil::dyn_cast<StoreVFGNode>(node)) {
            /* StoreVFGNode usages:
             * Largely symmetric with Load. Snipped for brevity.
             */
            SVFUtil::outs() << "Storing to object at " << svn->getValue()->getSourceLoc();
            const SVFGNode *def = vfg->getDefSVFGNode(svn->getPAGDstNode());
            /* Storing to struct/array */
            if (const GepVFGNode *gep_def = SVFUtil::dyn_cast<GepVFGNode>(def)) {
                const GepStmt *gs = SVFUtil::dyn_cast<GepStmt>(gep_def->getPAGEdge());
                SVFUtil::outs() << ", Index: " << gs->getConstantFieldIdx() << "\n";
            }
            /* Direct store */
            else if (const AddrVFGNode *addr_def = SVFUtil::dyn_cast<AddrVFGNode>(def)) {
                const AddrStmt *ads = SVFUtil::dyn_cast<AddrStmt>(addr_def->getPAGEdge());
                assert(ads);
                SVFUtil::outs() << "\n";
            }
            else {
                assert(false && "Store is not from a GEP or ADDR! Debug for more info!\n");
            }
        }
        else {
            // SVFUtil::outs() << "At VFG nodeID: " << node->getId() << ", type: " << node->getNodeKind() << "\n";
        }
    }
}

/* check whether the SRC of LOAD/DST of STORE is in our interested list */
void checkInterestedVFGCallback(const SVFG *vfg, Set<const VFGNode *> &visited, Set<NodeID> *interestedPtrs)
{
    for(Set<const VFGNode*>::const_iterator it = visited.begin(), eit = visited.end(); it!=eit; ++it)
    {
        const VFGNode* node = *it;
#ifdef USE_SVF_EX_DBOUT
        SVFUtil::outs() << "Checking VFG node " << node->getId() << "\n";
#endif
        /* For any load, if their source operand falls into interested set */
        if (const LoadVFGNode *ln = SVFUtil::dyn_cast<LoadVFGNode>(node)) {
            if (interestedPtrs->find(ln->getPAGSrcNodeID()) != interestedPtrs->end()) {
                SVFUtil::outs() << "Loading from " << ln->getPAGSrcNodeID() << ", location: " << ln->getValue()->getSourceLoc() << "\n";
            }
        } 
        /* For any store, if their destination operand falls into interested set */
        else if (const StoreVFGNode *svn = SVFUtil::dyn_cast<StoreVFGNode>(node)) {
            if (interestedPtrs->find(svn->getPAGDstNodeID()) != interestedPtrs->end()) {
                SVFUtil::outs() << "Storing to " << svn->getPAGDstNodeID() << ", location: " << svn->getValue()->getSourceLoc() << "\n";
            }
        }
    }
}

static DDAPass ddaForCallback;
/* check whether DDA query result of SRC of LOAD/DST of STORE is in our interested list */
void checkInterestedVFGCallbackDDA(const SVFG *vfg, Set<const VFGNode *> &visited, Set<NodeID> *interestedPtrs, NodeID pagHead)
{
    for(Set<const VFGNode*>::const_iterator it = visited.begin(), eit = visited.end(); it!=eit; ++it)
    {
        const VFGNode* node = *it;
#ifdef USE_SVF_EX_DBOUT
        SVFUtil::outs() << "Checking VFG node " << node->getId() << "\n";
        bool hit = false;
#endif
        /* For any load, if their source operand falls into interested set,
         * check if its query result has current VFG head 
         */
        if (const LoadVFGNode *ln = SVFUtil::dyn_cast<LoadVFGNode>(node)) {
            if (interestedPtrs->find(ln->getPAGSrcNodeID()) != interestedPtrs->end()) {
                const PointsTo &pts = ddaForCallback.makeQuery(ln->getPAGSrcNodeID());
                for (PointsTo::iterator it = pts.begin(), eit = pts.end(); it != eit; ++it) {
                    if (*it == pagHead) {
                        SVFUtil::outs() << "Loading from " << ln->getPAGSrcNodeID() << ", location: " << ln->getValue()->getSourceLoc();
                        if (pts.count() != 1)
                            SVFUtil::outs() << " (dubious)";
                        SVFUtil::outs() << "\n";
#ifdef USE_SVF_EX_DBOUT                        
                        hit = true;
#endif
                        break;
                    }
                }
#ifdef USE_SVF_EX_DBOUT
                if (hit == false) {
                    /* We are interested in this pointer,
                     * but its definition is not current variable we are watching.
                     * This means that strong updates happen and DDA has already found that for us.
                     */
                    SVFUtil::outs() << "Ignoring loading from " << ln->getPAGSrcNodeID() << ", location: " << ln->getValue()->getSourceLoc() << " (strong update)\n";
                }
#endif          
            }
        } 
        /* For any store, if their destination operand falls into interested set,
         * check if its query result has in current VFG head
         */
        else if (const StoreVFGNode *svn = SVFUtil::dyn_cast<StoreVFGNode>(node)) {
             if (interestedPtrs->find(svn->getPAGDstNodeID()) != interestedPtrs->end()) {
                const PointsTo &pts = ddaForCallback.makeQuery(svn->getPAGDstNodeID());
                for (PointsTo::iterator it = pts.begin(), eit = pts.end(); it != eit; ++it) {
                    if (*it == pagHead) {
                        SVFUtil::outs() << "Storing to " << svn->getPAGDstNodeID() << ", location: " << svn->getValue()->getSourceLoc();
                        if (pts.count() != 1)
                            SVFUtil::outs() << " (dubious)";
                        SVFUtil::outs() << "\n";
#ifdef USE_SVF_EX_DBOUT
                        hit = true;
#endif
                        break;
                    }
                }
#ifdef USE_SVF_EX_DBOUT
                if (hit == false) {
                    SVFUtil::outs() << "Ignoring storing to " << svn->getPAGDstNodeID() << ", location: " << svn->getValue()->getSourceLoc() << " (strong update)\n";
                }
#endif
            }
        }
    }
}

/*!
 * An example to query/collect all the uses of a definition of a value along value-flow graph (VFG)
 */
/* Note that given an `SVFValue`, there seems no way to find the actual PAG node it correspond to,
 * the only interfaces available are `getValueNode` and `getObjectNode`.
 * So I archive the original interfaces here, and use directly PAG id, which is loseless.
 */
// void traverseOnVFG(const SVFG* vfg, const SVFValue* val, Set<NodeID> *interestedPtrs = nullptr)
void traverseOnVFG(const SVFG* vfg, NodeID pagId, Set<NodeID> *interestedPtrs = nullptr)
{
    SVFIR* pag = SVFIR::getPAG();

    /* TODO: check the semantic of this line.
     * Currently, I view this as "finding the actual object".
     * Therefore, if we are holding the pointer of a glbvar, pNode is at its memory object I believe
     */
    PAGNode *origPNode = pag->getGNode(pagId);
    PAGNode* pNode = pag->getGNode(pag->getValueNode(origPNode->getValue()));
    const VFGNode* vNode = vfg->getDefSVFGNode(pNode);
    FIFOWorkList<const VFGNode*> worklist;
    Set<const VFGNode*> visited;
    worklist.push(vNode);

    /// Traverse along VFG
    SVFUtil::outs() << "-----\n";
    SVFUtil::outs() << "Finding accesses of global variable: " << origPNode->getValue()->getName() << ", VFG ID: " << vNode->getId() << ", PAG ID: " << pagId << "\n";
#ifdef USE_SVF_EX_DBOUT
    SVFUtil::outs() << "Finding childs of node " << pNode->getId() << " (value node)\n";
#endif
    while (!worklist.empty())
    {
        const VFGNode* vNode = worklist.pop();
        for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                    vNode->OutEdgeEnd(); it != eit; ++it)
        {
            VFGEdge* edge = *it;
            VFGNode* succNode = edge->getDstNode();
            if (visited.find(succNode) == visited.end())
            {
                visited.insert(succNode);
                worklist.push(succNode);
                // if (StmtVFGNode *tmp_node = SVFUtil::dyn_cast<StmtVFGNode>(succNode))
                //     SVFUtil::outs() << tmp_node->toString() << "\n";
#ifdef USE_SVF_EX_DBOUT
                SVFUtil::outs() << "Adding node " << succNode->getId() << "\n";
#endif
            }
        }
    }

    // singleLayerVFGCallback(vfg, visited);
    // checkInterestedVFGCallback(vfg, visited, interestedPtrs);
    checkInterestedVFGCallbackDDA(vfg, visited, interestedPtrs, pagId);
}

void getGlobalObject(std::vector<NodeID> &glbs)
{
    SVFIR* pag = SVFIR::getPAG();
    
    for(SVFIR::iterator it = pag->begin(), eit = pag->end(); it!=eit; it++)
    {
        PAGNode* pagNode = it->second;
        if (SVFUtil::isa<DummyValVar, DummyObjVar>(pagNode))
            continue;

        if(GepObjVar* gepobj = SVFUtil::dyn_cast<GepObjVar>(pagNode))
        {
            if(SVFUtil::isa<DummyObjVar>(pag->getGNode(gepobj->getBaseNode())))
                continue;
        }
        if(const SVFValue* val = pagNode->getValue())
        {
            /* TODO: find a way to differentiate instances of the same name */
            if(SVFUtil::isa<SVFGlobalValue>(val)) {
#ifdef USE_SVF_EX_DBOUT
                SVFUtil::outs() << "Finding global: " << val->getName() << ", at PAG id: " << pagNode->getId() << "\n";
#endif
                glbs.emplace_back(it->first);
            }
        }
    }
}

void getMonitoredPointer(std::vector<NodeID> &ptrs) 
{
    SVFIR* pag = SVFIR::getPAG();
    for(SVFIR::iterator it = pag->begin(), eit = pag->end(); it!=eit; it++)
    {
        PAGNode* pagNode = it->second;
        if (SVFUtil::isa<DummyValVar, DummyObjVar>(pagNode))
            continue;
        
        if (GepObjVar *gepobj = SVFUtil::dyn_cast<GepObjVar>(pagNode)) {
            if(SVFUtil::isa<DummyObjVar>(pag->getGNode(gepobj->getBaseNode())))
                continue;
            /* TODO */
            SVFUtil::outs() << "Id of PAG GEP node " << gepobj->getId() << "\n";
            ptrs.emplace_back(it->first);
        }

    }

}

void getGlobalRevPts(PointerAnalysis* pta, std::vector<NodeID> &glbs)
{
    for (auto id : glbs) {
        auto &RevPts = pta->getRevPts(id);
        SVFUtil::outs() << "Printing Reverse Points-to Set of NodeID " << id << ": ";
        for (auto &it : RevPts) {
            SVFUtil::outs() << it << " ";
        }
        SVFUtil::outs() << "\n";
    }
}

static Option<unsigned> valueIdx(
    "value-idx",
    "Index of variable wishes to be inspected",
    UINT_MAX
);

/* TODO: allow user to leave out bc file, directly select from these tests */
/* TODO: run tests automatically */
static unsigned valueIdxToGlobalIdx[] = {
    /* struct.bc */
    2, // struct.a -> 0
    3, // struct.b -> 1
    4, // struct.c -> 2

    /* multi-ptr.bc */
    1, // glb -> 3
    3, // glb2 -> 4

    /* multi-layer-dep.bc */
    1, // glb -> 5

    /* array.cc */
    2, // arr -> 6
    
    /* same-name.cc */
    1, // glb -> 7
    3, // glb2 -> 8

    /* main.bc (snort MRWE) */
    32 // _ZL12global_table
};

static void printPts(NodeID id, Set<NodeID> &s)
{
    SVFUtil::outs() << "Printing RevPts for node " << id << ", size: " << s.size() << "\n{";
    for (auto it : s) {
        SVFUtil::outs() << it << " ";
    }
    SVFUtil::outs() << "}\n";
}

int main(int argc, char ** argv)
{

    std::vector<std::string> moduleNameVec;
    moduleNameVec = OptionBase::parseOptions(
                        argc, argv, "Whole Program Points-to Analysis", "[options] <input-bitcode...>"
                    );

    if (Options::WriteAnder() == "ir_annotator")
    {
        LLVMModuleSet::preProcessBCs(moduleNameVec);
    }

    SVFModule* svfModule = LLVMModuleSet::buildSVFModule(moduleNameVec);

    /// Build Program Assignment Graph (SVFIR)
    SVFIRBuilder builder(svfModule);
    SVFIR* pag = builder.build();

    /// Create Andersen's pointer analysis
    Andersen* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

    /// Query aliases
    /// aliasQuery(ander,value1,value2);

    /// Print points-to information
    /// printPts(ander, value1);

    /// Call Graph
    PTACallGraph* callgraph = ander->getPTACallGraph();

    /// ICFG
    ICFG* icfg = pag->getICFG();
    // icfg->dump("icfg");

    /// Value-Flow Graph (VFG)
    VFG* vfg = new VFG(callgraph);

    /// Sparse value-flow graph (SVFG)
    SVFGBuilder svfBuilder(true);
    SVFG* svfg = 
    svfBuilder.buildFullSVFG(ander);

    /// Collect uses of an LLVM Value
    std::vector<NodeID> globals;
    getGlobalObject(globals);

    /* initialze a DDA pass
     * Note that DDA object is declared as global 
     * since I don't want to pass it in arguments
     */
    ddaForCallback.runInternalUse(pag);

    /* If value idx is not set, inspect all global variables */
    if (valueIdx() == UINT_MAX) {
        /* TODO: eliminate code duplication */
        for (auto gid : globals) {
            Set<NodeID> interestedPtrs = ander->getRevPts(gid);
#ifdef USE_SVF_EX_DBOUT
            printPts(gid, interestedPtrs);
#endif
            // std::vector<NodeID> ptrs;
            // getMonitoredPointer(ptrs);
            traverseOnVFG(svfg, gid, &interestedPtrs);
        }
    } else {
        /* TODO: check if this copy is bad */
        unsigned gid = valueIdxToGlobalIdx[valueIdx()];
        Set<NodeID> interestedPtrs = ander->getRevPts(globals[gid]);
#ifdef USE_SVF_EX_DBOUT
        printPts(globals[gid], interestedPtrs);
#endif
        traverseOnVFG(svfg, gid, &interestedPtrs);
    }
    
    // getGlobalRevPts(ander, globals);

    // SVFUtil::outs() << printPts(ander, globals[2]);


    /// Collect all successor nodes on ICFG
    for (const auto &it : *icfg)
    {
        const ICFGNode* node = it.second;
        traverseOnICFG(icfg, node);
    }

    // clean up memory
    delete vfg;
    AndersenWaveDiff::releaseAndersenWaveDiff();
    SVFIR::releaseSVFIR();

    LLVMModuleSet::getLLVMModuleSet()->dumpModulesToFile(".svf.bc");
    SVF::LLVMModuleSet::releaseLLVMModuleSet();

    llvm::llvm_shutdown();
    return 0;
}

