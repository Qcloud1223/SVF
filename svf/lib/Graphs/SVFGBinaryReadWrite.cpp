#include "SVFIR/SVFModule.h"
#include "Util/SVFUtil.h"
#include "Graphs/SVFG.h"
#include "Graphs/SVFGStat.h"
#include "MemoryModel/PointerAnalysisImpl.h"
#include "Util/Options.h"

#include <iostream>
#include <fstream>

/* Utilize MMIO to read ASAP */
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>

using namespace SVF;
using namespace SVFUtil;
using namespace std;

#define likely(x)       __builtin_expect(!!(x), 1)
#define unlikely(x)     __builtin_expect(!!(x), 0)

static inline unsigned writeNodeWorker(
    unsigned *writeBuffer,
    NodeID vfgID, VFGNode::VFGNodeK ty, NodeID icfgID,
    const MRVer *mrver,
    std::ofstream &f)
{
    /* format: 
        0: *whole size (4) (max size 65536 unsigned)
        1: node ID (4)
        2: node type (1 -> 4) 
        3: ICFG node ID (4)
        4: MR VER ID (4)
        5: MRVERSION (4) 
        6: MSSADef (4)
        7: *MemRegion array length (4)
        8: *Def MemRegion array length (4)
        MemRegion array (4*m)
        Def MemRegion array (4*n)

        In total: 8 + (m + n) unsigned
        Reserve buffer size = 65536 unsigned, so (m + n) should lt 65527
    */
   /* Note that whole size stands for length after it, 
    * such that we don't have to minus 1 when we read it later 
    */
    auto mrArrayLen = mrver->getMR()->getPointsTo().count();
    auto defArrayLen = mrver->getDef()->getMR()->getPointsTo().count();
    if (unlikely(mrArrayLen + defArrayLen > 65527))
        assert(false && "Max buffer dump reached! try double the default buffer size");
    unsigned realSize = mrArrayLen + defArrayLen + 8;
    writeBuffer[0] = realSize;
    writeBuffer[1] = vfgID;
    writeBuffer[2] = ty;
    writeBuffer[3] = icfgID;
    writeBuffer[4] = mrver->getID();
    writeBuffer[5] = mrver->getSSAVersion();
    writeBuffer[6] = mrver->getDef()->getType();
    writeBuffer[7] = mrArrayLen;
    writeBuffer[8] = defArrayLen;
    unsigned idx = 9;
    for (auto ii : mrver->getMR()->getPointsTo()) 
        writeBuffer[idx++] = ii;
    for (auto ii : mrver->getDef()->getMR()->getPointsTo())
        writeBuffer[idx++] = ii;
    
    f.write(reinterpret_cast<const char *>(writeBuffer), idx * sizeof(unsigned));
    return idx;
}

static inline unsigned writeNoMRverWorker(
    unsigned *writeBuffer,
    NodeID srcVfgID, NodeID dstVfgID, VFGNode::VFGNodeK ty,
    bool intra,
    std::ofstream &f)
{
    /* format:
      0: whole length (4)
      1: src node ID (4)
      2: node type (4)
      3: dst node ID (4)
      4: (optional) intra (4)
     */
    /* use 1 unsigned long as the flag, such that we know from length if it's intra */
    writeBuffer[0] = (intra ? 4 : 3);
    writeBuffer[1] = srcVfgID;
    writeBuffer[2] = ty;
    writeBuffer[3] = dstVfgID;

    f.write(reinterpret_cast<const char *>(writeBuffer), (writeBuffer[0] + 1) * sizeof(unsigned));
    return writeBuffer[0] + 1;
}

static inline unsigned writeOpVerWorker(
    unsigned *writeBuffer,
    const MSSAPHISVFGNode *phiNode,
    std::ofstream &f)
{
    /* idx 0 reserved for whole size in unsigned */
    unsigned idx = 1;
    unsigned consumed = 0;
    for (MemSSA::PHI::OPVers::const_iterator it = phiNode->opVerBegin(), eit = phiNode->opVerEnd();
                    it != eit; it++)
    {
        const auto mrver = it->second;
        /* layout:
            0: *whole size for *this* mrver
            1: MR VER ID (4)
            2: MRVERSION (4)
            3: MSSADef (4)
            4: *MemRegion array length (4)
            5: *Def MemRegion array length (4)
            MemRegion array (4*m)
            Def MemRegion array (4*n)

            In total: 6 + (m + n) unsigned 
         */
        auto mrArrayLen = mrver->getMR()->getPointsTo().count();
        auto defArrayLen = mrver->getDef()->getMR()->getPointsTo().count(); 
        consumed += mrArrayLen + defArrayLen + 6;
        if (unlikely(consumed > 65535))
            assert(false && "Max buffer dump reached for OpVer! try double the default buffer size");
        /* length not include the first one */
        writeBuffer[idx++] = mrArrayLen + defArrayLen + 5;
        writeBuffer[idx++] = mrver->getID();
        writeBuffer[idx++] = mrver->getSSAVersion();
        writeBuffer[idx++] = mrver->getDef()->getType();
        writeBuffer[idx++] = mrArrayLen;
        writeBuffer[idx++] = defArrayLen;
        for (auto ii : mrver->getMR()->getPointsTo())
            writeBuffer[idx++] = ii;
        for (auto ii : mrver->getDef()->getMR()->getPointsTo())
            writeBuffer[idx++] = ii;
    }
    writeBuffer[0] = consumed;

    f.write(reinterpret_cast<const char *>(writeBuffer), (consumed + 1) * sizeof(unsigned));
    return consumed + 1;
}

static inline MRVer *readMRver(const unsigned *buffer)
{
    auto mrverID = buffer[0];
    auto mrVersion = buffer[1];
    auto mssaDef = buffer[2];
    auto mrArrayLen = buffer[3];
    auto defArrayLen = buffer[4];

    NodeBS dstPts;
    for (auto i = 0; i < mrArrayLen; i++) {
        dstPts.set(buffer[5 + i]);
    }
    MemRegion *tempMemRegion = new MemRegion(dstPts);

    MSSADEF *tempDef;
    tempDef = new MSSADEF(static_cast<MSSADEF::DEFTYPE>(mssaDef), tempMemRegion);

    MRVer *tempMRVer;
    tempMRVer = new MRVer(tempMemRegion, mrVersion, tempDef);

    return tempMRVer;
}

/* 
 * Write Nodes
 */
void SVFG::writeNodeToFile(const string &filename)
{
    outs() << "Writing binary SVFG nodes to '" << filename + "-nodes" << "'...\n";
    error_code err;
    // std::fstream f(filename.c_str(), std::ios_base::out);
    std::ofstream f(filename + "-nodes", std::ios::binary);
    if (!f.good())
    {
        outs() << "  error opening file for writing!\n";
        return;
    }

    unsigned *writeBuffer = new unsigned[65536];
    // unsigned debugIdx = 2;
    for (const auto &it : IDToNodeMap) {
        auto vfgID = it.first;
        const auto &node = it.second;
        if (const auto formalIn = SVFUtil::dyn_cast<FormalINSVFGNode>(node)) {
            // outs() << debugIdx++ << " writing " <<
            writeNodeWorker(writeBuffer, vfgID, VFGNode::FPIN, formalIn->getFunEntryNode()->getId(), formalIn->getMRVer(), f);
            // outs() << "\n";
        }
        else if (const auto formalOut = SVFUtil::dyn_cast<FormalOUTSVFGNode>(node)) {
            // outs() << debugIdx++ << " writing " <<
            writeNodeWorker(writeBuffer, vfgID, VFGNode::FPOUT, formalOut->getFunExitNode()->getId(), formalOut->getMRVer(), f);
            // outs() << "\n";
        }
        else if (const auto actualIn = SVFUtil::dyn_cast<ActualINSVFGNode>(node)) {
            // outs() << debugIdx++ << " writing " <<
            writeNodeWorker(writeBuffer, vfgID, VFGNode::APIN, actualIn->getCallSite()->getId(), actualIn->getMRVer(), f);
            // outs() << "\n";
        }
        else if (const auto actualOut = SVFUtil::dyn_cast<ActualOUTSVFGNode>(node)) {
            // outs() << debugIdx++ << " writing " <<
            writeNodeWorker(writeBuffer, vfgID, VFGNode::APOUT, actualOut->getCallSite()->getId(), actualOut->getMRVer(), f);
            // outs() << "\n";
        }
        else if (const auto phiNode = SVFUtil::dyn_cast<MSSAPHISVFGNode>(node)) {
            const auto &inst = phiNode->getICFGNode()->getBB()->front();
            // outs() << debugIdx++ << " writing " <<
            writeNodeWorker(writeBuffer, vfgID, VFGNode::MPhi, pag->getICFG()->getICFGNode(inst)->getId(), phiNode->getResVer(), f);
            writeOpVerWorker(writeBuffer, phiNode, f);
            // outs() << "\n";
        }
    }
    f.close();
}


/* 
 * Write Edges
 */
void SVFG::writeEdgeToFile(const string &filename)
{
    outs() << "Writing binary SVFG edges to '" << filename + "-edges" << "'...\n";
    error_code err;
    std::ofstream f(filename + "-edges", std::ios::binary);
    if (!f.good())
    {
        outs() << "  error opening file for writing!\n";
        return;
    }
    
    unsigned *writeBuffer = new unsigned[65536];

    for (const auto &it : IDToNodeMap) {
        auto vfgID = it.first;
        const auto &node = it.second;
        if (const auto loadNode = SVFUtil::dyn_cast<LoadSVFGNode>(node)) {
            const auto &muSet = mssa->getMUSet(SVFUtil::cast<LoadStmt>(loadNode->getPAGEdge()));
            for (const auto it : muSet) {
                if (const auto mu = SVFUtil::dyn_cast<LOADMU>(it)) {
                    /* Note: abuse the node worker since they has the same format */
                    writeNodeWorker(writeBuffer, vfgID, VFGNode::Load, getDef(mu->getMRVer()), mu->getMRVer(), f);
                }
            }
        }
        else if (const auto storeNode = SVFUtil::dyn_cast<StoreSVFGNode>(node)) {
            const auto &chiSet = mssa->getCHISet(SVFUtil::cast<StoreStmt>(storeNode->getPAGEdge()));
            for (const auto it : chiSet) {
                if (const auto chi = SVFUtil::dyn_cast<STORECHI>(it)) {
                    writeNodeWorker(writeBuffer, vfgID, VFGNode::Store, getDef(chi->getOpVer()), chi->getOpVer(), f);
                }
            }
        }
        else if (const auto formalIn = SVFUtil::dyn_cast<FormalINSVFGNode>(node)) {
            PTACallGraphEdge::CallInstSet callInstSet;
            mssa->getPTA()->getPTACallGraph()->getDirCallSitesInvokingCallee(formalIn->getFun(),callInstSet);
            for (const auto &cs : callInstSet) {
                if (!mssa->hasMU(cs))
                    continue;
                const auto &actualIns = getActualINSVFGNodes(cs);
                for (const auto &ait: actualIns) {
                    const auto &actualIn = SVFUtil::cast<ActualINSVFGNode>(getSVFGNode(ait));
                    /* formalIn does not have additional fields */
                    writeNoMRverWorker(writeBuffer, vfgID, actualIn->getId(), VFGNode::FPIN, false, f);
                }
            }
        }
        else if (const auto formalOut = SVFUtil::dyn_cast<FormalOUTSVFGNode>(node)) {
            PTACallGraphEdge::CallInstSet callInstSet;
            mssa->getPTA()->getPTACallGraph()->getDirCallSitesInvokingCallee(formalOut->getFun(),callInstSet);
            for (const auto &cs : callInstSet) {
                if (!mssa->hasCHI(cs))
                    continue;
                const auto &actualOuts = getActualOUTSVFGNodes(cs);
                for (const auto &ait : actualOuts) {
                    const auto &actualOut = SVFUtil::cast<ActualOUTSVFGNode>((getSVFGNode(ait)));
                    writeNoMRverWorker(writeBuffer, vfgID, actualOut->getId(), VFGNode::FPOUT, false, f);
                }
            }
            const auto def = getDef(formalOut->getMRVer());
            writeNoMRverWorker(writeBuffer, vfgID, def, VFGNode::FPOUT, true, f);
        }
        else if (const auto actualIn = SVFUtil::dyn_cast<ActualINSVFGNode>(node)) {
            const auto def = getDef(actualIn->getMRVer());
            writeNoMRverWorker(writeBuffer, vfgID, def, VFGNode::APIN, false, f);
        }
        else if (const auto phiNode = SVFUtil::dyn_cast<MSSAPHISVFGNode>(node)) {
            for (MemSSA::PHI::OPVers::const_iterator it = phiNode->opVerBegin(), eit = phiNode->opVerEnd();
                    it != eit; it++)
            {
                const auto mrver = it->second;
                const auto def = getDef(mrver);
                writeNodeWorker(writeBuffer, vfgID, VFGNode::MPhi, def, mrver, f);
            }
        }
    }
    f.close();
}

/* 
 * Read Node and Edge file to rebuild SVFG
 */
void SVFG::readBinaryFile(const string &filename)
{
    string nodeFilename = filename + "-nodes";
    string edgeFilename = filename + "-edges";
    int nodeFd = open(nodeFilename.c_str(), O_RDONLY);
    int edgeFd = open(edgeFilename.c_str(), O_RDONLY);
    if (nodeFd == -1 || edgeFd == -1) {
        outs() << "cannot open binary file!\n";
        return;
    }
    
    struct stat nodeFile;
    struct stat edgeFile;
    fstat(nodeFd, &nodeFile);
    fstat(edgeFd, &edgeFile);
    
    /* file size in number of unsigned */
    auto nodeSize = nodeFile.st_size >> 2;
    assert((nodeSize << 2) == nodeFile.st_size);
    auto edgeSize = edgeFile.st_size >> 2;
    assert((edgeSize << 2) == edgeFile.st_size);

    const unsigned *nodeStart = static_cast<const unsigned *>(
        mmap(NULL, nodeFile.st_size, PROT_READ, MAP_PRIVATE, nodeFd, 0)
    );
    if (nodeStart == MAP_FAILED) {
        outs() << "mmap for node failed because " << errno << "\n";
        return;
    }

    const unsigned *edgeStart = static_cast<const unsigned *>(
        mmap(NULL, edgeFile.st_size, PROT_READ, MAP_PRIVATE, edgeFd, 0)
    );
    if (edgeStart == MAP_FAILED) {
        outs() << "mmap for edge failed because " << errno << "\n";
        return;
    }

    /* restore begins */
    PAGEdge::PAGEdgeSetTy& stores = getPAGEdgeSet(PAGEdge::Store);
    for (PAGEdge::PAGEdgeSetTy::iterator iter = stores.begin(), eiter =
                stores.end(); iter != eiter; ++iter)
    {
        StoreStmt* store = SVFUtil::cast<StoreStmt>(*iter);
        const StmtSVFGNode* sNode = getStmtVFGNode(store);
        for(CHISet::iterator pi = mssa->getCHISet(store).begin(), epi = mssa->getCHISet(store).end(); pi!=epi; ++pi)
            setDef((*pi)->getResVer(),sNode);
    }

    /* add nodes */
    stat->ATVFNodeStart();
    // unsigned debugIdx = 2;
    while (nodeSize) {
        unsigned sz = nodeStart[0];
        auto vfgId = nodeStart[1];
        switch (nodeStart[2]) {
            case VFGNode::FPIN:
                addFormalINSVFGNode(
                    SVFUtil::dyn_cast<FunEntryICFGNode>(pag->getICFG()->getICFGNode(nodeStart[3])),
                    readMRver(nodeStart + 4),
                    vfgId
                    );
                // outs() << debugIdx++ << " Reading a FPIN node :" << vfgId << "\n";
                break;
            case VFGNode::FPOUT:
                addFormalOUTSVFGNode(
                    SVFUtil::dyn_cast<FunExitICFGNode>(pag->getICFG()->getICFGNode(nodeStart[3])),
                    readMRver(nodeStart + 4),
                    vfgId
                );
                // outs() << debugIdx++ << " Reading a FPOUT node: " << vfgId << "\n";
                break;
            case VFGNode::APIN:
                addActualINSVFGNode(
                    SVFUtil::dyn_cast<CallICFGNode>(pag->getICFG()->getICFGNode(nodeStart[3])),
                    readMRver(nodeStart + 4),
                    vfgId
                );
                // outs() << debugIdx++ << " Reading a APIN node: " << vfgId << "\n";
                break;
            case VFGNode::APOUT:
                addActualOUTSVFGNode(
                    SVFUtil::dyn_cast<CallICFGNode>(pag->getICFG()->getICFGNode(nodeStart[3])),
                    readMRver(nodeStart + 4),
                    vfgId
                );
                // outs() << debugIdx++ << " Reading a APOUT node: " << vfgId << "\n";
                break;
            case VFGNode::MPhi:
            {
                Map<u32_t, const MRVer *> OPVers;
                int index = 0;
                auto opverOff = nodeStart[0] + 1;
                auto icfgNodeId = nodeStart[3];
                const auto &mrver = readMRver(nodeStart + 4);
                /* nodeStart is now at OPVer whole length */
                nodeStart += opverOff;
                /* the length for the whole opver section */
                auto opverSz = nodeStart[0];
                /* nodeStart is now at first OPVer */
                nodeStart += 1;
                nodeSize -= 1;
                while (opverSz > 0) {
                    /* the whole MRVer include size */
                    opverSz -= nodeStart[0] + 1;
                    /* parse each MRVer */
                    OPVers.insert(make_pair(index, readMRver(nodeStart + 1)));
                    /* adjust size according to PHI node */
                    nodeSize -= nodeStart[0] + 1;
                    // outs() << "\tnode read: " << nodeStart[0] + 1 << "\n";
                    nodeStart += nodeStart[0] + 1;
                }
                addIntraMSSAPHISVFGNode(pag->getICFG()->getICFGNode(icfgNodeId), OPVers.begin(), OPVers.end(), mrver, vfgId);
                /* In order to conform to default increment of nodeStart,
                 * decrease there to stay consistent
                 */
                nodeStart -= opverOff;
                // outs() << debugIdx++ << " Reading a MPHI node: " << vfgId << "\n";
                break;
            }
            default:
                // outs() << "Unrecognized node type: " << nodeStart[2] << "!\n";
                assert(false);
        }
        if (totalVFGNode < vfgId)
            totalVFGNode = vfgId + 1;
        
        nodeStart += sz + 1;
        nodeSize -= sz + 1;
        // outs() << "\tnode read: " << sz + 1 << "\n";
    }
    stat->ATVFNodeEnd();

    /* edges */
    // debugIdx = 180;
    stat->indVFEdgeStart();
    while (edgeSize) {
        auto src = edgeStart[1];
        auto dst = edgeStart[3];
        switch (edgeStart[2])
        {
        case VFGNode::FPIN:
        {
            const auto &formalIn = SVFUtil::cast<FormalINSVFGNode>(getSVFGNode(src));
            const auto &actualIn = SVFUtil::cast<ActualINSVFGNode>(getSVFGNode(dst));
            addInterIndirectVFCallEdge(actualIn, formalIn, getCallSiteID(actualIn->getCallSite(), formalIn->getFun()));
            // outs() << debugIdx++ << " Reading a FPIN edge from:" << src << "\n";
            break;
        }
            
        case VFGNode::FPOUT:
        {
            const auto &formalOut = SVFUtil::cast<FormalOUTSVFGNode>(getSVFGNode(src));
            if (edgeStart[0] == 4) {
                /* intra */
                addIntraIndirectVFEdge(dst, src, formalOut->getMRVer()->getMR()->getPointsTo());
            } else {
                const auto &actualOut = SVFUtil::cast<ActualOUTSVFGNode>(getSVFGNode(dst));
                addInterIndirectVFRetEdge(formalOut, actualOut, getCallSiteID(actualOut->getCallSite(), formalOut->getFun()));
            }
            // outs() << debugIdx++ << " Reading a FPOUT edge from:" << src << "\n";
            break;
        }
        
        case VFGNode::APIN:
        {
            const auto &actualIn = SVFUtil::cast<ActualINSVFGNode>(getSVFGNode(src));
            addIntraIndirectVFEdge(dst, src, actualIn->getMRVer()->getMR()->getPointsTo());
            // outs() << debugIdx++ << " Reading a APIN edge from:" << src << "\n";
            break;
        }
        
        case VFGNode::APOUT:
            break;
        
        case VFGNode::Store:
        case VFGNode::Load:
        case VFGNode::MPhi:
        {
            MRVer *tempMRVer;
            tempMRVer = readMRver(edgeStart + 4);
            addIntraIndirectVFEdge(dst, src, tempMRVer->getMR()->getPointsTo());
            // outs() << debugIdx++ << " Reading a Store/Load/MPHI edge from:" << src << "\n";
            break;
        }

        default:
            // outs() << "Type " << edgeStart[2] << " unexpected!\n";
            assert(false);
            break;
        }
        edgeSize -= edgeStart[0] + 1;
        edgeStart += edgeStart[0] + 1;
    }
    stat->indVFEdgeEnd();
    connectFromGlobalToProgEntry();
}