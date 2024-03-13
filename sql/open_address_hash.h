#pragma once

#include <cstring>
#include <my_dbug.h>
#include <m_string.h>
#include <my_global.h>
#include <m_ctype.h>

namespace traits
{
template<typename Key>
struct Open_address_hash_key_trait;

template<typename Value>
struct Open_address_hash_value_trait;
}

template <typename Key, typename Value,
          typename Key_trait=traits::Open_address_hash_key_trait<Key>,
          typename Value_trait=traits::Open_address_hash_value_trait<Value> >
class Open_address_hash
{
  static const Key *get_key(const Value &elem)
  { return Key_trait::get_key(elem); }
  static bool is_empty(const Value &el) { return Value_trait::is_empty(el); }
  bool is_equal(const Value &lhs, const Value &rhs)
  { return Value_trait::is_equal(lhs, rhs); }
  static constexpr Value EMPTY= Value_trait::EMPTY;
public:
  using Hash_value_type= typename Key_trait::Hash_value_type;

  Open_address_hash()
  {
    first.set_mark(true);
    first.set_ptr(EMPTY);
    second= EMPTY;
  }

  ~Open_address_hash()
  {
    if (!first.mark())
    {
      DBUG_ASSERT(hash_array);
      free(hash_array);
    }
  }

private:
  Hash_value_type to_index(const Hash_value_type &hash_value)
  {
    return hash_value & ((1 << capacity_power) - 1);
  }

  Hash_value_type hash_from_value(const Value &value)
  {
    return Key_trait::get_hash_value(get_key(value));
  }

  bool insert_into_bucket(const Value &value)
  {
    auto hash_val= to_index(hash_from_value(value));

    while (!is_empty(hash_array[hash_val]))
    {
      if (is_equal(hash_array[hash_val], value))
        return false;
      hash_val= to_index(hash_val + 1);
    }

    hash_array[hash_val]= value;
    return true;
  };

  uint rehash_subsequence(uint i)
  {
    for (uint j= to_index(i + 1); !is_empty(hash_array[j]); j= to_index(j + 1))
    {
      auto temp_el= hash_array[j];
      if (to_index(hash_from_value(temp_el)) == j)
        continue;
      hash_array[j]= EMPTY;
      insert_into_bucket(temp_el);
    }

    return i;
  }

  bool erase_from_bucket(const Value &value)
  {
    for (auto key= to_index(Key_trait::get_hash_value(get_key(value)));
         !is_empty(hash_array[key]); key= to_index(key + 1))
    {
      if (is_equal(hash_array[key], value))
      {
        hash_array[key]= EMPTY;
        rehash_subsequence(key);
        return true;
      }
    }

    return false;
  }

  bool grow(const uint64 new_capacity_power)
  {
    DBUG_ASSERT(new_capacity_power > capacity_power);
    uint64 past_capacity= 1 << capacity_power;
    uint64 capacity= 1 << new_capacity_power;
    capacity_power= new_capacity_power;
    hash_array= (Value *) realloc(hash_array, capacity * sizeof(Value));
    if (!hash_array)
      return false;
    bzero(hash_array + past_capacity,
          (capacity - past_capacity) * sizeof(Value*));

    for (uint i= 0; i < capacity; i++)
    {
      if (hash_array[i] && i != to_index(hash_from_value(hash_array[i])))
      {
        auto temp_el= hash_array[i];
        hash_array[i]= EMPTY;
        insert_into_bucket(temp_el);
      }
    }
    return true;
  }

  void shrink(const uint64 new_capacity_power)
  {
    DBUG_ASSERT(new_capacity_power < capacity_power);
    uint64 past_capacity= 1 << capacity_power;
    uint64 capacity= 1 << new_capacity_power;
    capacity_power= new_capacity_power;

    for (uint i= capacity; i < past_capacity; i++)
    {
      if (hash_array[i])
      {
        auto temp_el= hash_array[i];
        insert_into_bucket(temp_el);
      }
    }

    hash_array= (Value *) realloc(hash_array, capacity * sizeof(Value));
  }


  bool init_hash_array()
  {
    Value _first= first.ptr();
    Value _second= second;

    capacity_power= CAPACITY_POWER_INITIAL;
    hash_array= (Value*)calloc(1 << capacity_power, sizeof (Value*));
    _size= 0;

    if (!insert_into_bucket(_first))
      return false;
    _size++;
    if (!insert_into_bucket(_second))
      return false;
    _size++;

    return true;
  }

public:
  Value find(const Value &elem)
  {
    return find(*Key_trait::get_key(elem),
                [&elem](const Value &rhs) { return rhs == elem; });
  }

  template <typename Func>
  Value find(const Key &key, const Func &elem_suits)
  {
    if (first.mark())
    {
      if (first.ptr() && elem_suits(first.ptr()))
        return first.ptr();
      if (!is_empty(second) && elem_suits(second))
        return second;

      return EMPTY;
    }

    for (auto idx= to_index(Key_trait::get_hash_value(&key));
         !is_empty(hash_array[idx]); idx= to_index(idx + 1))
    {
      if (elem_suits(hash_array[idx]))
        return hash_array[idx];
    }

    return EMPTY;
  };

  bool erase(const Value &value)
  {
    if (first.mark())
    {
      if (!is_empty(first.ptr()) && is_equal(first.ptr(), value))
      {
        first.set_ptr(EMPTY);
        return true;
      }
      else if (second && is_equal(second, value))
      {
        second= EMPTY;
        return true;
      }
      return false;
    }

    const uint64_t capacity= 1 << capacity_power;
    if (unlikely(capacity > 7 && (_size - 1) * LOW_LOAD_FACTOR < capacity))
      shrink(capacity_power - 1);

    if (!erase_from_bucket(value))
      return false;
    _size--;
    return true;
  }

  bool insert(const Value &value)
  {
    if (first.mark())
    {
      if (is_empty(first.ptr()))
      {
        if (is_equal(second, value))
          return false;
        first.set_ptr(value);
        return true;
      }
      else if (is_empty(second))
      {
        if (is_equal(first.ptr(), value))
          return false;
        second= value;
        return true;
      }
      else
      {
        first.set_mark(false);
        if (!init_hash_array())
          return false;
      }
    }

    if (unlikely(_size == UINT32_MAX))
      return false;

    bool res= true;
    const uint64 capacity= 1 << capacity_power;
    if (unlikely((_size + 1) * MAX_LOAD_FACTOR > capacity))
      res= grow(capacity_power + 1);

    res= res && insert_into_bucket(value);
    if (res)
      _size++;
    return res;
  };

  bool clear()
  {
    if (first.mark())
    {
      first.set_ptr(EMPTY);
      second= EMPTY;
      return true;
    }
    if (!hash_array)
      return false;

    free(hash_array);
    capacity_power= CAPACITY_POWER_INITIAL;

    first.set_mark(true);
    first.set_ptr(EMPTY);
    second= EMPTY;

    return true;
  }

  uint32 size()
  { 
    if (first.mark())
    {
      uint32 ret_size= 0;
      if (!is_empty(first.ptr()))
        ret_size++;
      if (!is_empty(second))
        ret_size++;
      return ret_size;
    }
    else
    {
      return _size; 
    }
  }
  uint32 buffer_size(){ return first.mark() ? 0 : 1 << capacity_power; }

private:
  static constexpr uint CAPACITY_POWER_INITIAL= 3;
  static constexpr int MAX_LOAD_FACTOR= 2;
  static constexpr int LOW_LOAD_FACTOR= 10;

  class markable_reference
  {
  public:
    static constexpr uintptr_t MARK_MASK = 1ULL << 63;

    void set_ptr(Value ptr)
    {
      p = reinterpret_cast<uintptr_t>(ptr) | (p & MARK_MASK);
    }

    Value ptr(){ return reinterpret_cast<Value>(p & ~MARK_MASK); }

    void set_mark(bool mark)
    {
      p = (p & ~MARK_MASK) | (static_cast<uintptr_t>(mark) << 63);
    }

    bool mark()
    {
      return p & MARK_MASK;
    }

  private:
    uintptr_t p;
  };

  union
  {
    struct
    {
      markable_reference first;
      Value second;
    };
    struct
    {
      Value *hash_array;
      uint64 capacity_power: 6;
      uint64 _size: 58;
    };
  };
};

namespace traits
{

template<typename Key>
struct Open_address_hash_key_trait
{
  public:
  using Hash_value_type= ulong;

  static Hash_value_type get_hash_value(const Key *key)
  {
    ulong nr1= 1, nr2= 4;
    my_ci_hash_sort(&my_charset_bin, (uchar*) key, sizeof (Key), &nr1, &nr2);
    return (Hash_value_type) nr1;
  }
  /**
   Function returning key based on value, needed to be able to rehash the table
   on expansion. Value should be able to return Key from itself.
   The provided instantiation implements "set", i.e. Key matches Value
  */
  static Key *get_key(Key *value) { return value; }
};

template<typename Value>
struct Open_address_hash_value_trait
{
  static_assert(sizeof (Value) <= sizeof (uintptr_t),
                "The plain-type Value can only be specified for elements of a bucket size. "
                "You may have wanted to specify Value=Your_value_type*.");
  static bool is_equal(const Value &lhs, const Value &rhs)
  { return lhs == rhs; }
  /** The following two methods have to be specialized for non-scalar Value */
  static bool is_empty(const Value el)
  { return el == 0; }
};

template<typename T>
struct Open_address_hash_value_trait<T*>
{
  static bool is_equal(const T *lhs, const T *rhs)
  { return lhs == rhs; }
  static bool is_empty(const T* el) { return el == nullptr; }
  static constexpr T *EMPTY= NULL;
};

}
