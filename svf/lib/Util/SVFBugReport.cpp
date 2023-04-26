//===- SVFBugReport.cpp -- Base class for statistics---------------------------------//
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
//===----------------------------------------------------------------------===//


//
// Created by JoelYang on 2023/4/19.
//

#include "Util/SVFBugReport.h"
#include <cassert>
#include "Util/cJSON.h"
#include "Util/SVFUtil.h"
#include <sstream>
#include <fstream>

using namespace std;
using namespace SVF;

const std::string GenericBug::getLoc() const
{
    const GenericEvent *sourceInstEvent = bugEventStack.at(bugEventStack.size() -1);
    assert(SourceInstEvent::classof(sourceInstEvent) && "bugEventStack top should be a SourceInst event");
    return sourceInstEvent->getEventLoc();
}

const std::string GenericBug::getFuncName() const
{
    const GenericEvent *sourceInstEvent = bugEventStack.at(bugEventStack.size() -1);
    assert(SourceInstEvent::classof(sourceInstEvent) && "bugEventStack top should be a SourceInst event");
    return sourceInstEvent->getFuncName();
}

cJSON *BufferOverflowBug::getBugDescription() const
{
    cJSON *bugDescription = cJSON_CreateObject();
    cJSON *allocLB = cJSON_CreateNumber(allocLowerBound);
    cJSON *allocUB = cJSON_CreateNumber(allocUpperBound);
    cJSON *accessLB = cJSON_CreateNumber(accessLowerBound);
    cJSON *accessUB = cJSON_CreateNumber(accessUpperBound);

    cJSON_AddItemToObject(bugDescription, "AllocLowerBound", allocLB);
    cJSON_AddItemToObject(bugDescription, "AllocUpperBound", allocUB);
    cJSON_AddItemToObject(bugDescription, "AccessLowerBound", accessLB);
    cJSON_AddItemToObject(bugDescription, "AccessUpperBound", accessUB);

    return bugDescription;
}

void BufferOverflowBug::printBugToTerminal() const
{
    stringstream bugInfo;
    if(FullBufferOverflowBug::classof(this))
    {
        SVFUtil::errs() << SVFUtil::bugMsg1("\t Full Overflow :") <<  " accessing at : ("
                        << GenericBug::getLoc() << ")\n";

    }
    else
    {
        SVFUtil::errs() << SVFUtil::bugMsg1("\t Partial Overflow :") <<  " accessing at : ("
                        << GenericBug::getLoc() << ")\n";
    }
    bugInfo << "\t\t  allocate size : [" << allocLowerBound << ", " << allocUpperBound << "], ";
    bugInfo << "access size : [" << accessLowerBound << ", " << accessUpperBound << "]\n";
    SVFUtil::errs() << "\t\t Info : \n" << bugInfo.str();
    SVFUtil::errs() << "\t\t Events : \n";

    for(auto eventPtr : bugEventStack)
    {
        switch(eventPtr->getEventType())
        {
        case GenericEvent::CallSite:
        {
            SVFUtil::errs() << "\t\t  callsite at : ( " << eventPtr->getEventLoc() << " )\n";
            break;
        }
        default:   // TODO: implement more events when needed
        {
            break;
        }
        }
    }

}

cJSON * NeverFreeBug::getBugDescription() const
{
    cJSON *bugDescription = cJSON_CreateObject();
    return bugDescription;
}

void NeverFreeBug::printBugToTerminal() const
{
    SVFUtil::errs() << SVFUtil::bugMsg1("\t NeverFree :") <<  " memory allocation at : ("
                    << GenericBug::getLoc() << ")\n";
}

cJSON * PartialLeakBug::getBugDescription() const
{
    cJSON *bugDescription = cJSON_CreateObject();
    cJSON *pathInfo = cJSON_CreateArray();
    auto lastBranchEventIt = bugEventStack.end() - 1;
    for(auto eventIt = bugEventStack.begin(); eventIt != lastBranchEventIt; eventIt++)
    {
        cJSON *newBranch = cJSON_CreateObject();
        cJSON *branchLoc = cJSON_Parse((*eventIt)->getEventLoc().c_str());
        if(branchLoc == nullptr) branchLoc = cJSON_CreateObject();
        cJSON *branchCondition = cJSON_CreateString((*eventIt)->getEventDescription().c_str());

        cJSON_AddItemToObject(newBranch, "BranchLoc", branchLoc);
        cJSON_AddItemToObject(newBranch, "BranchCond", branchCondition);

        cJSON_AddItemToArray(pathInfo, newBranch);
    }

    cJSON_AddItemToObject(bugDescription, "ConditionalFreePath", pathInfo);

    return bugDescription;
}

void PartialLeakBug::printBugToTerminal() const
{
    SVFUtil::errs() << SVFUtil::bugMsg2("\t PartialLeak :") <<  " memory allocation at : ("
                    << GenericBug::getLoc() << ")\n";

    SVFUtil::errs() << "\t\t conditional free path: \n";
    auto lastBranchEventIt = bugEventStack.end() - 1;
    for(auto eventIt = bugEventStack.begin(); eventIt != lastBranchEventIt; eventIt++)
    {
        SVFUtil::errs() << "\t\t  --> (" << (*eventIt)->getEventLoc() << "|" << (*eventIt)->getEventDescription() << ") \n";
    }
    SVFUtil::errs() << "\n";
}

cJSON * DoubleFreeBug::getBugDescription() const
{
    cJSON *bugDescription = cJSON_CreateObject();

    cJSON *pathInfo = cJSON_CreateArray();
    auto lastBranchEventIt = bugEventStack.end() - 1;
    for(auto eventIt = bugEventStack.begin(); eventIt != lastBranchEventIt; eventIt++)
    {
        cJSON *newBranch = cJSON_CreateObject();
        cJSON *branchLoc = cJSON_Parse((*eventIt)->getEventLoc().c_str());
        if(branchLoc == nullptr) branchLoc = cJSON_CreateObject();
        cJSON *branchCondition = cJSON_CreateString((*eventIt)->getEventDescription().c_str());

        cJSON_AddItemToObject(newBranch, "BranchLoc", branchLoc);
        cJSON_AddItemToObject(newBranch, "BranchCond", branchCondition);

        cJSON_AddItemToArray(pathInfo, newBranch);
    }
    cJSON_AddItemToObject(bugDescription, "DoubleFreePath", pathInfo);

    return bugDescription;
}

void DoubleFreeBug::printBugToTerminal() const
{
    SVFUtil::errs() << SVFUtil::bugMsg2("\t Double Free :") <<  " memory allocation at : ("
                    << GenericBug::getLoc() << ")\n";

    SVFUtil::errs() << "\t\t double free path: \n";
    auto lastBranchEventIt = bugEventStack.end() - 1;
    for(auto eventIt = bugEventStack.begin(); eventIt != lastBranchEventIt; eventIt++)
    {
        SVFUtil::errs() << "\t\t  --> (" << (*eventIt)->getEventLoc() << "|" << (*eventIt)->getEventDescription() << ") \n";
    }
    SVFUtil::errs() << "\n";
}

cJSON * FileNeverCloseBug::getBugDescription() const
{
    cJSON *bugDescription = cJSON_CreateObject();
    return bugDescription;
}

void FileNeverCloseBug::printBugToTerminal() const
{
    SVFUtil::errs() << SVFUtil::bugMsg1("\t FileNeverClose :") <<  " file open location at : ("
                    << GenericBug::getLoc() << ")\n";
}

cJSON * FilePartialCloseBug::getBugDescription() const
{
    cJSON *bugDescription = cJSON_CreateObject();

    cJSON *pathInfo = cJSON_CreateArray();

    auto lastBranchEventIt = bugEventStack.end() - 1;
    for(auto eventIt = bugEventStack.begin(); eventIt != lastBranchEventIt; eventIt++)
    {
        cJSON *newBranch = cJSON_CreateObject();
        cJSON *branchLoc = cJSON_Parse((*eventIt)->getEventLoc().c_str());
        if(branchLoc == nullptr) branchLoc = cJSON_CreateObject();
        cJSON *branchCondition = cJSON_CreateString((*eventIt)->getEventDescription().c_str());

        cJSON_AddItemToObject(newBranch, "BranchLoc", branchLoc);
        cJSON_AddItemToObject(newBranch, "BranchCond", branchCondition);

        cJSON_AddItemToArray(pathInfo, newBranch);
    }
    cJSON_AddItemToObject(bugDescription, "ConditionalFileClosePath", pathInfo);

    return bugDescription;
}

void FilePartialCloseBug::printBugToTerminal() const
{
    SVFUtil::errs() << SVFUtil::bugMsg2("\t PartialFileClose :") <<  " file open location at : ("
                    << GenericBug::getLoc() << ")\n";

    SVFUtil::errs() << "\t\t conditional file close path: \n";
    auto lastBranchEventIt = bugEventStack.end() - 1;
    for(auto eventIt = bugEventStack.begin(); eventIt != lastBranchEventIt; eventIt++)
    {
        SVFUtil::errs() << "\t\t  --> (" << (*eventIt)->getEventLoc() << "|" << (*eventIt)->getEventDescription() << ") \n";
    }
    SVFUtil::errs() << "\n";
}

const std::string CallSiteEvent::getFuncName() const
{
    return callSite->getCallSite()->getFunction()->getName();
}

const std::string CallSiteEvent::getEventLoc() const
{
    return callSite->getCallSite()->getSourceLoc();
}

const std::string CallSiteEvent::getEventDescription() const
{
    std::string description("calls ");
    const SVFFunction *callee = SVFUtil::getCallee(callSite->getCallSite());
    if(callee == nullptr)
    {
        description += "<unknown>";
    }
    else
    {
        description += callee->getName();
    }
    return description;
}

const std::string BranchEvent::getFuncName() const
{
    return branchInst->getFunction()->getName();
}

const std::string BranchEvent::getEventLoc() const
{
    return branchInst->getSourceLoc();
}

const std::string BranchEvent::getEventDescription() const
{
    if (branchSuccessFlg)
    {
        return "True";
    }
    else
    {
        return "False";
    }
}

const std::string SourceInstEvent::getFuncName() const
{
    return sourceSVFInst->getFunction()->getName();
}

const std::string SourceInstEvent::getEventLoc() const
{
    return sourceSVFInst->getSourceLoc();
}

const std::string SourceInstEvent::getEventDescription() const
{
    return "None";
}

SVFBugReport::~SVFBugReport()
{
    for(auto bugIt: bugSet)
    {
        delete bugIt;
    }
    for(auto eventPtr:eventSet)
    {
        delete eventPtr;
    }
}

void SVFBugReport::dumpToJsonFile(const std::string& filePath)
{
    std::map<GenericEvent::EventType, std::string> eventType2Str =
    {
        {GenericEvent::CallSite, "call site"},
        {GenericEvent::Caller, "caller"},
        {GenericEvent::Loop, "loop"},
        {GenericEvent::Branch, "branch"}
    };

    std::map<GenericBug::BugType, std::string> bugType2Str =
    {
        {GenericBug::FULLBUFOVERFLOW, "Full Buffer Overflow"},
        {GenericBug::PARTIALBUFOVERFLOW, "Partial Buffer Overflow"},
        {GenericBug::NEVERFREE, "Never Free"},
        {GenericBug::PARTIALLEAK, "Partial Leak"},
        {GenericBug::FILENEVERCLOSE, "File Never Close"},
        {GenericBug::FILEPARTIALCLOSE, "File Partial Close"},
        {GenericBug::DOUBLEFREE, "Double Free"}
    };

    ofstream jsonFile(filePath, ios::out);

    jsonFile << "{";

    size_t commaCounter = bugSet.size() - 1;  // comma num needed
    for(auto bugPtr : bugSet)
    {
        cJSON *singleBug = cJSON_CreateObject();

        /// add bug information to json
        cJSON *bugType = cJSON_CreateString(bugType2Str[bugPtr->getBugType()].c_str());
        cJSON_AddItemToObject(singleBug, "DefectType", bugType);

        cJSON *bugLoc = cJSON_Parse(bugPtr->getLoc().c_str());
        if(bugLoc == nullptr)
        {
            bugLoc = cJSON_CreateObject();
        }
        cJSON_AddItemToObject(singleBug, "Location", bugLoc);

        cJSON *bugFunction = cJSON_CreateString(bugPtr->getFuncName().c_str());
        cJSON_AddItemToObject(singleBug, "Function", bugFunction);

        cJSON_AddItemToObject(singleBug, "Description", bugPtr->getBugDescription());

        /// add event information to json
        cJSON *eventList = cJSON_CreateArray();
        const GenericBug::EventStack bugEventStack = bugPtr->getEventStack();
        if(BufferOverflowBug::classof(bugPtr))   // add only when bug is context sensitive
        {
            for(auto eventPtr : bugEventStack)
            {
                if (SourceInstEvent::classof(eventPtr))
                {
                    continue;
                }

                cJSON *singleEvent = cJSON_CreateObject();
                //event type
                cJSON *eventType = cJSON_CreateString(eventType2Str[eventPtr->getEventType()].c_str());
                cJSON_AddItemToObject(singleEvent, "EventType", eventType);
                //function name
                cJSON *eventFunc = cJSON_CreateString(eventPtr->getFuncName().c_str());
                cJSON_AddItemToObject(singleEvent, "Function", eventFunc);
                //event loc
                cJSON *eventLoc = cJSON_Parse(eventPtr->getEventLoc().c_str());
                if(eventLoc == nullptr)
                {
                    eventLoc = cJSON_CreateObject();
                }
                cJSON_AddItemToObject(singleEvent, "Location", eventLoc);
                //event description
                cJSON *eventDescription = cJSON_CreateString(eventPtr->getEventDescription().c_str());
                cJSON_AddItemToObject(singleEvent, "Description", eventDescription);

                cJSON_AddItemToArray(eventList, singleEvent);
            }
        }
        cJSON_AddItemToObject(singleBug, "Events", eventList);

        /// dump single bug to json str and write to file
        char *singleBugStr = cJSON_Print(singleBug);
        jsonFile << singleBugStr;
        if (commaCounter != 0)
        {
            jsonFile << ",\n";
        }
        commaCounter --;

        /// destroy the cJSON object
        cJSON_Delete(singleBug);
    }

    jsonFile << "}";
    jsonFile.close();
}