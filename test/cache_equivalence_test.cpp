#include <cstdint>
#include <vector>

#include <gtest/gtest.h>
#include <algebra/finite_fields/finite_fields.hpp>

using namespace algebra;

using F = FiniteField<11, 3>;
using E = F::Element;

namespace {

// All 1331 field elements, in index order 0..1330.
std::vector<E> all_elements() {
    std::vector<E> elements;
    elements.reserve(F::cardinality());
    for (std::uint64_t i = 0; i < F::cardinality(); ++i) {
        elements.push_back(E::from_index(i));
    }
    return elements;
}

// The original multiply, written out by hand so it bypasses the cache:
// multiply the polynomials, then reduce modulo the field's modulus.
E original_multiply(const E& a, const E& b) {
    return E::from_polynomial(a.representative().multiply(b.representative()));
}

//orig add helper
E original_add(const E& a, const E& b) {
    return E::from_polynomial(a.representative().add(b.representative()));
}

// orig neg helper
E original_negate(const E& a) {
    return E::from_polynomial(a.representative().negate());
}

}

TEST(CacheEquivalence, MultiplyMatchesOriginalForEveryPair) {
    const auto elements = all_elements();
    // Pass 0 starts with an empty cache (misses fill it); pass 1 reads from it (hits).
    for (int pass = 0; pass < 2; ++pass) {
        for (std::size_t i = 0; i < elements.size(); ++i) {
            for (std::size_t j = 0; j < elements.size(); ++j) {
                ASSERT_EQ(elements[i].multiply(elements[j]),
                          original_multiply(elements[i], elements[j]))
                    << "pass " << pass << ", i " << i << ", j " << j;
            }
        }
    }
}

TEST(CacheEquivalence, AddMatchesOriginalForEveryPair) {
    const auto elements = all_elements();
    for (int pass = 0; pass < 2; pass++) {
        for (std::size_t i = 0; i < elements.size(); i++) {
            for (std::size_t j = 0; j < elements.size(); j++) {
                ASSERT_EQ(elements[i].add(elements[j]),
                          original_add(elements[i], elements[j]))
                    << "pass " << pass << ", i " << i << ", j " << j;
            }
        }
    }
}

TEST(CacheEquivalence, NegateMatchesOriginal) {
    const auto elements = all_elements();
    for (int pass = 0; pass < 2; pass++) {
        for (std::size_t i = 0; i < elements.size(); i++) {
            ASSERT_EQ(elements[i].negate(), original_negate(elements[i])) << "i " << i;
        }
    }
}

TEST(CacheEquivalence, ReciprocalIsTheInverse) {
    const auto elements = all_elements();
    for (int pass = 0; pass < 2; ++pass) {
        for (std::size_t i = 1; i < elements.size(); ++i) { //loops from 1 cause i=0 doesn't have an inverse cause duh lol
            const E inverse = elements[i].reciprocal();
            ASSERT_TRUE(original_multiply(elements[i], inverse).is_one()) << "i " << i;
        }
    }
}

TEST(CacheEquivalence, IndexRoundTripsForEveryElement) {
    for (int pass = 0; pass < 2; ++pass) {
        for (std::uint64_t i = 0; i < F::cardinality(); ++i) { 
            ASSERT_EQ(E::get_index(E::from_index(i).representative()), i);
        }
    }
}

