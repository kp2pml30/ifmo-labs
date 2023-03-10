import { Component } from '@angular/core';
import { Observable } from 'rxjs';
import { Currency } from '../currencies';

export type ProductData = {
  name: string,
  price: number
}

@Component({
  selector: 'app-product',
  templateUrl: './product.component.html',
  styleUrls: ['./product.component.css']
})
export class ProductComponent {
  pd: ProductData|undefined
  price: number = 0
  curr: string = ""

  initialize(pd: ProductData, c: Currency, ob: Observable<Currency>) {
    this.pd = pd
    const upd = (v: Currency) => {
      this.curr = `${pd.price * v.coef}${v.sign}`
      //this.price = v.
    }
    upd(c)
    ob.subscribe(upd)
  }
}
