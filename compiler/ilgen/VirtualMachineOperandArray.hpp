/*******************************************************************************
 *
 * (c) Copyright IBM Corp. 2017
 *
 *  This program and the accompanying materials are made available
 *  under the terms of the Eclipse Public License v1.0 and
 *  Apache License v2.0 which accompanies this distribution.
 *
 *      The Eclipse Public License is available at
 *      http://www.eclipse.org/legal/epl-v10.html
 *
 *      The Apache License v2.0 is available at
 *      http://www.opensource.org/licenses/apache2.0.php
 *
 * Contributors:
 *    Multiple authors (IBM Corp.) - initial implementation and documentation
 *******************************************************************************/

#ifndef OMR_VIRTUALMACHINEOPERANDARRAY_INCL
#define OMR_VIRTUALMACHINEOPERANDARRAY_INCL

#include <stdint.h>
#include "ilgen/VirtualMachineRegister.hpp"
#include "ilgen/IlBuilder.hpp"

namespace TR { class MethodBuilder; }

namespace OMR
{

/**
 * @brief simulates an operand array used by many bytecode based virtual machines
 * In such virtual machines, the operand array holds the intermediate expression values
 * computed by the bytecodes. The compiler simulates this operand array as well, but
 * what is modified from the simulated operand array are expression nodes
 * that represent the value computed by the bytecodes.
 *
 * The array is represented as an array of pointers to TR::IlValue's, making it
 * easy to use IlBuilder services to consume and compute new values. 
 *
 * The current implementation does not share anything among different
 * VirtualMachineOperandArray objects. Possibly, some of the state could be
 * shared to save some memory. For now, simplicity is the goal.
 *
 * VirtualMachineOperandArray implements VirtualMachineState:
 * Commit() simply iterates over the simulated operand array and stores each
 *   value onto the virtual machine's operand array (more details at definition).
 * Reload() read the virtual machine array back into the simulated operand array
 * MakeCopy() copies the state of the operand array
 * MergeInto() is slightly subtle. Operations may have been already created
 *   below the merge point, and those operations will have assumed the
 *   expressions are stored in the TR::IlValue's for the state being merged
 *   *to*. So the purpose of MergeInto() is to store the values of the current
 *   state into the same variables as in the "other" state.
 * UpdateArray() update OperandArray_base so Reload/Commit will use the right
 *    if the array moves in memory
 *
 */

class VirtualMachineOperandArray : public VirtualMachineState
   {
   public:
   /**
    * @brief public constructor, must be instantiated inside a compilation because uses heap memory
    * @param mb TR::MethodBuilder object of the method currently being compiled
    * @param numOfElements the number of elements in the array
    */
   VirtualMachineOperandArray(TR::MethodBuilder *mb, int32_t numOfElements, TR::IlType *elementType, VirtualMachineRegister *arrayBase);
   /**
    * @brief constructor used to copy the array from another state
    * @param other the operand array whose values should be used to initialize this object
    */
   VirtualMachineOperandArray(VirtualMachineOperandArray *other);

   /**
    * @brief write the simulated operand array to the virtual machine
    * @param b the builder where the operations will be placed to recreate the virtual machine operand array
    */
   virtual void Commit(TR::IlBuilder *b);
   
   /**
    * @brief read the virtual machine array back into the simulated operand array
    * @param b the builder where the operations will be placed to recreate the simulated operand array
    * stack accounts for new or dropped virtual machine stack elements. 
    */
   virtual void Reload(TR::IlBuilder *b);

   /**
    * @brief create an identical copy of the current object.
    * @returns the copy of the current object
    */
   virtual VirtualMachineState *MakeCopy();

   /**
    * @brief emit operands to store current operand array values into same variables as used in another operand array
    * @param other operand array for the builder object control is merging into
    * @param b builder object where the operations will be added to make the current operand array the same as the other
    */
   virtual void MergeInto(OMR::VirtualMachineState *other, TR::IlBuilder *b);
   
   /**
    * @brief update the values used to read and write the virtual machine array
    * @param b the builder where the values will be placed
    * @param array the new array base address.
    */
   virtual void UpdateArray(TR::IlBuilder *b, TR::IlValue *array);

   /**
    * @brief Returns the expression at the given index of the simulated operand array
    * @param index the location of the expression to return
    * @returns the expression at the given index
    */
   virtual TR::IlValue *Get(int32_t index);
   
   /**
    * @brief Set the expression into the simulated operand array at the given index
    * @param index the location to store the expression
    * @param value expression to store into the simulated operand array
    */
   virtual void Set(int32_t index, TR::IlValue *value);
  
   /**
    * @brief Move the expression from one index to another index in the simulated operand array
    * @param dstIndex the location to store the expression
    * @param srcIndex the location to copy the expression from
    */ 
   virtual void Move(TR::IlBuilder *b, int32_t dstIndex, int32_t srcIndex);

   private:
   TR::MethodBuilder *_mb;
   int32_t _numberOfElements;
   OMR::VirtualMachineRegister *_arrayBaseRegister;
   TR::IlType *_elementType;
   TR::IlValue **_values;
   };
}

#endif // !defined(OMR_VIRTUALMACHINEOPERANDARRAY_INCL)
