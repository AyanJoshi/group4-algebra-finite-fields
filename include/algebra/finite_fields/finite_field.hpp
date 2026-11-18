#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <ostream>
#include <stdexcept>
#include <utility>
#include <algebra/finite_fields/modulus.hpp>
#include <vector>

namespace algebra {

template<std::uint32_t P, std::size_t K = 1, class ModulusPolicy = FirstEnumeratedIrreducible>
class FiniteField;

template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class UncachedFiniteFieldElement : public AdditiveOperators<UncachedFiniteFieldElement<P, K, ModulusPolicy>>,
                           public MultiplicativeOperators<UncachedFiniteFieldElement<P, K, ModulusPolicy>>,
                           public DivisionOperators<UncachedFiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    using parent_type = FiniteField<P, K, ModulusPolicy>;
    using algebra = FieldDescriptor;
    using coefficient_type = PrimeFieldElement<P>;
    using polynomial_type = Polynomial<coefficient_type>;

private:
    polynomial_type value_;
    struct Reduced {};

    UncachedFiniteFieldElement(polynomial_type value, Reduced) : value_(std::move(value)) {}

public:
    UncachedFiniteFieldElement() {
        static_cast<void>(parent_type::modulus());
    }

    static UncachedFiniteFieldElement from_polynomial(const polynomial_type& value) {
        polynomial_type remainder = value % parent_type::modulus();
        return UncachedFiniteFieldElement(std::move(remainder), Reduced{});
    }

    static UncachedFiniteFieldElement from_coefficients(std::initializer_list<std::int64_t> values) {
        polynomial_type value;
        std::size_t index = 0;
        for (const auto coefficient : values) {
            value.set_coefficient(index++, coefficient_type::from_integer(coefficient));
        }
        return from_polynomial(value);
    }

    static UncachedFiniteFieldElement from_integer(std::int64_t value) {
        return from_polynomial(polynomial_type{coefficient_type::from_integer(value)});
    }

    static UncachedFiniteFieldElement from_index(std::uint64_t index) {
        if (index >= parent_type::cardinality()) {
            throw std::out_of_range("Finite field element index is out of range");
        }
        polynomial_type value;
        for (std::size_t i = 0; i < K; ++i) {
            value.set_coefficient(i, coefficient_type::from_index(index % P));
            index /= P;
        }
        return from_polynomial(value);
    }

    static UncachedFiniteFieldElement zero() {
        return UncachedFiniteFieldElement{};
    }

    static UncachedFiniteFieldElement one() {
        return from_integer(1);
    }

    UncachedFiniteFieldElement add(const UncachedFiniteFieldElement& other) const {
        const polynomial_type sum = value_.add(other.value_);
        return from_polynomial(sum);
    }

    UncachedFiniteFieldElement negate() const {
        return from_polynomial(value_.negate());
    }

    UncachedFiniteFieldElement multiply(const UncachedFiniteFieldElement& other) const {
        const polynomial_type product = value_.multiply(other.value_);
        return from_polynomial(product);
    }

    UncachedFiniteFieldElement reciprocal() const {
        if (is_zero()) {
            throw std::domain_error("Zero has no reciprocal");
        }
        polynomial_type previous_remainder = parent_type::modulus();
        polynomial_type remainder = value_;
        polynomial_type previous_coefficient = polynomial_type::zero();
        polynomial_type coefficient = polynomial_type::one();
        while (!remainder.is_zero()) {
            auto division = previous_remainder.divmod(remainder);
            polynomial_type next_remainder = std::move(division.second);
            polynomial_type next_coefficient =
                previous_coefficient - division.first.multiply(coefficient);
            previous_remainder = std::move(remainder);
            remainder = std::move(next_remainder);
            previous_coefficient = std::move(coefficient);
            coefficient = std::move(next_coefficient);
        }
        if (previous_remainder.degree() != 0) {
            throw std::logic_error("The element is not invertible for this modulus");
        }
        const coefficient_type scale = previous_remainder.coefficient(0).reciprocal();
        return from_polynomial(previous_coefficient.scale_left(scale));
    }

    bool is_zero() const {
        return value_.is_zero();
    }

    bool is_one() const {
        return value_.is_one();
    }

    coefficient_type coefficient(std::size_t index) const {
        if (index >= K) {
            throw std::out_of_range("Finite field coefficient index is out of range");
        }
        return value_.coefficient(index);
    }

    std::array<coefficient_type, K> coefficients() const {
        std::array<coefficient_type, K> result{};
        for (std::size_t i = 0; i < K; ++i) {
            result[i] = value_.coefficient(i);
        }
        return result;
    }

    const polynomial_type& representative() const {
        return value_;
    }

    const parent_type& parent() const {
        static const parent_type instance;
        return instance;
    }

    bool operator==(const UncachedFiniteFieldElement& other) const {
        return value_ == other.value_;
    }

    friend std::ostream& operator<<(std::ostream& out, const UncachedFiniteFieldElement& value) {
        return out << value.value_;
    }
};

// Answer tables for one field, built once from the original (uncached) arithmetic.
// Element numbers are base-P digits: c0 + P*c1 + P^2*c2 + ...
template<std::uint32_t P, std::size_t K, class ModulusPolicy>
struct FiniteFieldTables {
    using Uncached = UncachedFiniteFieldElement<P, K, ModulusPolicy>;
    using polynomial_type = typename Uncached::polynomial_type;

    std::uint64_t size = 0;                    // number of elements (1331 for 11^3)
    std::vector<polynomial_type> polynomial;   // polynomial[i]: the element numbered i
    std::vector<std::uint16_t> add;            // add[a * size + b]: number of a + b
    std::vector<std::uint16_t> multiply;       // multiply[a * size + b]: number of a * b
    std::vector<std::uint16_t> negate;         // negate[a]: number of -a
    std::vector<std::uint16_t> reciprocal;     // reciprocal[a]: number of 1/a (a != 0)

    // Number of a reduced polynomial: same formula as Wendell's get_index.
    static std::uint64_t index_of(const polynomial_type& value) {
        std::uint64_t index = 0;
        std::uint64_t place = 1;
        for (std::size_t degree = 0; degree < K; ++degree) {
            index += value.coefficient(degree).representative() * place;
            place *= P;
        }
        return index;
    }

    FiniteFieldTables() {
        size = FiniteField<P, K, ModulusPolicy>::cardinality();
        if (size > 65536) {
            throw std::length_error("Field is too large for 16-bit element tables");
        }
        std::vector<Uncached> elements;
        elements.reserve(size);
        polynomial.reserve(size);
        for (std::uint64_t i = 0; i < size;i++) {
            elements.push_back(Uncached::from_index(i));
            polynomial.push_back(elements.back().representative());
        }
        add.resize(size * size);
        multiply.resize(size * size);
        negate.resize(size);
        reciprocal.resize(size);
        
        // for (int a = 0; a<=size-1;a++) {
        //     negate[a] = (-1)*a;
        //     if(a!=0) {
        //         reciprocal[a] = 1/a;
        //     }
        //     for (int b=0; b<=size-1;b++) {
        //         add[a*size+b] = a+b;
        //         multiply[a*size+b] = a*b;
        //     }
        // }

        for (std::uint64_t a=0; a<size; a++) {
            negate[a] = static_cast<std::uint16_t>(index_of(elements[a].negate().representative()));
            if (!elements[a].is_zero()) {
                reciprocal[a] = static_cast<std::uint16_t>(index_of(elements[a].reciprocal().representative()));/* same pattern, using elements[a].reciprocal() */;
            }
            for (std::uint64_t b=0; b<size; b++) {
                add[a * size + b] = static_cast<std::uint16_t>(index_of(elements[a].add(elements[b]).representative()));
                multiply[a * size + b] = static_cast<std::uint16_t>(index_of(elements[a].multiply(elements[b]).representative()));
            }
        }
    }

    // Built the first time anyone asks, then reused for the rest of the program.
    static const FiniteFieldTables& get() {
        static const FiniteFieldTables tables;
        return tables;
    }
};

// Cached element:stores only its number and answers every operation from
// FiniteFieldTables
template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class FiniteFieldElement : public AdditiveOperators<FiniteFieldElement<P, K, ModulusPolicy>>,
                           public MultiplicativeOperators<FiniteFieldElement<P, K, ModulusPolicy>>,
                           public DivisionOperators<FiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    using parent_type = FiniteField<P, K, ModulusPolicy>;
    using algebra = FieldDescriptor;
    using coefficient_type = PrimeFieldElement<P>;
    using polynomial_type = Polynomial<coefficient_type>;

private:
    using Uncached = UncachedFiniteFieldElement<P, K, ModulusPolicy>;
    using Tables = FiniteFieldTables<P, K, ModulusPolicy>;

    std::uint16_t index_ = 0;  // this element's number; 0 is the zero element

    struct FromIndex {};
    FiniteFieldElement(std::uint64_t index, FromIndex) : index_(static_cast<std::uint16_t>(index)) {}

public:
    // Number of a reduced polynomial. Kept because the MPI code uses it.
    static std::uint64_t get_index(const polynomial_type& value) {
        return Tables::index_of(value);
    }

    FiniteFieldElement() {
        static_cast<void>(parent_type::modulus());
    }

    // Reduce with the original arithmetic, then keep only the number.
    static FiniteFieldElement from_polynomial(const polynomial_type& value) {
        const Uncached reduced = Uncached::from_polynomial(value);
        return FiniteFieldElement(Tables::index_of(reduced.representative()), FromIndex{});
    }

    static FiniteFieldElement from_coefficients(std::initializer_list<std::int64_t> values) {
        polynomial_type value;
        std::size_t index = 0;
        for (const auto coefficient : values) {
            value.set_coefficient(index++, coefficient_type::from_integer(coefficient));
        }
        return from_polynomial(value);
    }

    static FiniteFieldElement from_integer(std::int64_t value) {
        return from_polynomial(polynomial_type{coefficient_type::from_integer(value)});
    }

    static FiniteFieldElement from_index(std::uint64_t index) {
        if (index >= parent_type::cardinality()) {
            throw std::out_of_range("Finite field element index is out of range");
        }
        static_cast<void>(parent_type::modulus());
        return FiniteFieldElement(index, FromIndex{});
    }

    static FiniteFieldElement zero() {
        return FiniteFieldElement{};
    }

    static FiniteFieldElement one() {
        return from_integer(1);
    }

    FiniteFieldElement add(const FiniteFieldElement& other) const {
        const Tables& tables = Tables::get();
        return FiniteFieldElement(tables.add[index_ * tables.size + other.index_], FromIndex{});
    }

    FiniteFieldElement negate() const {
        return FiniteFieldElement(Tables::get().negate[index_], FromIndex{});
    }

    FiniteFieldElement multiply(const FiniteFieldElement& other) const {
        const Tables& tables = Tables::get();
        return FiniteFieldElement(tables.multiply[index_ * tables.size + other.index_], FromIndex{});
    }

    FiniteFieldElement reciprocal() const {
        if (is_zero()) {
            throw std::domain_error("Zero has no reciprocal");
        }
        return FiniteFieldElement(Tables::get().reciprocal[index_], FromIndex{});
    }

    bool is_zero() const {
        return index_ == 0;
    }

    bool is_one() const {
        return index_ == 1;
    }

    coefficient_type coefficient(std::size_t index) const {
        if (index >= K) {
            throw std::out_of_range("Finite field coefficient index is out of range");
        }
        return representative().coefficient(index);
    }

    std::array<coefficient_type, K> coefficients() const {
        std::array<coefficient_type, K> result{};
        for (std::size_t i = 0; i < K; ++i) {
            result[i] = representative().coefficient(i);
        }
        return result;
    }

    // The polynomial lives in the table; the element only stores its number.
    const polynomial_type& representative() const {
        return Tables::get().polynomial[index_];
    }

    const parent_type& parent() const {
        static const parent_type instance;
        return instance;
    }

    bool operator==(const FiniteFieldElement& other) const {
        return index_ == other.index_;
    }

    friend std::ostream& operator<<(std::ostream& out, const FiniteFieldElement& value) {
        return out << value.representative();
    }
};

template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class FiniteField : public FieldStructure<FiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    using Element = FiniteFieldElement<P, K, ModulusPolicy>;
    using Base = PrimeField<Cyclic<P>>;
    using PolynomialType = typename Element::polynomial_type;
    static constexpr std::uint32_t characteristic = P;
    static constexpr std::size_t extension_degree = K;

    FiniteField() {
        initialize();
    }

    static const PolynomialType& modulus() {
        static const PolynomialType value = [] {
            PolynomialType candidate = ModulusPolicy::template polynomial<P, K>();
            if (candidate.degree() != K || !candidate.leading_coefficient().is_one() ||
                !is_irreducible(candidate)) {
                throw std::invalid_argument("The modulus must be monic and irreducible with degree K");
            }
            return candidate;
        }();
        return value;
    }

    static void initialize() {
        static_cast<void>(modulus());
    }

    static std::uint64_t cardinality() {
        return checked_power(P, K);
    }

    static Element element(std::initializer_list<std::int64_t> values) {
	return Element::from_coefficients(values);
    }

    static Element element(std::int64_t value) {
	return Element::from_integer(value);
    }

    static Element zero() {
        return Element::zero();
    }

    static Element one() {
        return Element::one();
    }

    static Element alpha() {
        return Element::from_polynomial(PolynomialType::variable());
    }
};

}
